use {crate::{history::History, pruned::Pruned, record::Record},
     regex::RegexSet,
     std::{error::Error,
           io::{BufRead, Read, Write}}};


fn main() -> Result<(), Box<dyn Error>> {
    use std::{env,
              fs::File,
              io::{self, BufReader},
              path::PathBuf};

    let input_files: Vec<File> = env::args().skip(1).map(File::open).collect::<Result<_, _>>()?;

    fn default_ignores_filename() -> Result<PathBuf, env::VarError> {
        env::var("HOME").map(|home| {
            PathBuf::from(home).join(".config/my/bash/interactive/history/ignores.regexes")
        })
    }
    let ignores_filename =
        env::var("MY_BASH_HISTORY_COMBINER_IGNORES").map(PathBuf::from).or_else(|e| match e {
            env::VarError::NotPresent => default_ignores_filename(),
            env::VarError::NotUnicode(_) => Err(e),
        })?;
    let ignores_file = File::open(ignores_filename)
        .map(|file| Some(BufReader::new(file)))
        .or_else(|e| if e.kind() == io::ErrorKind::NotFound { Ok(None) } else { Err(e) })?;

    combine_and_prune(input_files, ignores_file, &mut io::stdout().lock())
}


fn combine_and_prune(
    input_files: impl IntoIterator<Item = impl Read>,
    ignores_file: Option<impl BufRead>,
    out: &mut impl Write,
) -> Result<(), Box<dyn Error>> {
    //
    let inputs: Vec<History> =
        input_files.into_iter().map(History::new).collect::<Result<_, _>>()?;

    let ignores = if let Some(ignores_file) = ignores_file {
        let ignores_lines: Vec<String> = ignores_file.lines().collect::<Result<_, _>>()?;
        RegexSet::new(ignores_lines)?
    } else {
        RegexSet::empty()
    };

    let records = inputs.iter().flat_map(History::iter);

    let pruned = {
        let mut status = Ok(());
        let records = records.map_while(|result| match result {
            Ok(record) => Some(record),
            Err(e) => {
                status = Err(e); // Capture first error.
                None // Stop iterating.
            },
        });
        let pruned = Pruned::new(records, ignores);
        status.map(|()| pruned)
    }?;

    pruned.dump(out)?;
    Ok(())
}


mod record {
    use std::fmt::{self, Display, Formatter};

    #[derive(Copy, Clone, Debug, Eq, PartialEq)]
    pub struct Record<'l> {
        pub entire:  &'l str,
        pub command: &'l str,
    }

    impl Display for Record<'_> {
        fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result { f.write_str(self.entire) }
    }
}


mod history {
    use {crate::Record,
         std::io::{self, Read}};

    pub struct History {
        backing: String,
    }

    impl History {
        pub fn new(mut input_file: impl Read) -> Result<Self, io::Error> {
            let mut backing = String::new();
            input_file.read_to_string(&mut backing)?;
            Ok(Self { backing })
        }

        pub fn iter(&self) -> impl Iterator<Item = Result<Record<'_>, String>> {
            Iter { cur: &self.backing }
        }
    }

    struct Iter<'l> {
        cur: &'l str,
    }

    impl<'l> Iterator for Iter<'l> {
        type Item = Result<Record<'l>, String>;

        fn next(&mut self) -> Option<Self::Item> {
            if self.cur.is_empty() {
                None
            } else {
                Some({
                    let next;
                    if let Some(cmd_start) = advance_past::timestamp(self.cur) {
                        if let Some(cmd_end) = advance_past::command(self.cur, cmd_start) {
                            next = Ok(Record {
                                entire:  &self.cur[.. cmd_end],
                                command: &self.cur[cmd_start .. cmd_end - 1],
                            });
                            self.cur = &self.cur[cmd_end ..];
                        } else {
                            next = Err(&self.cur[cmd_start ..])
                        }
                    } else {
                        next = Err(self.cur)
                    }

                    next.map_err(|s| {
                        let stop = s.find('\n').unwrap_or_else(|| 55.min(s.len()));
                        format!(
                            "malformed: {:?}{}",
                            &s[.. stop],
                            if stop < s.len() { "..." } else { "" }
                        )
                    })
                })
            }
        }
    }

    #[cfg(test)]
    mod tests {
        use {super::*, std::io::Cursor};
        #[test]
        fn basic() {
            fn check<const N: usize>(input: &str, expected: [Result<Record<'_>, &str>; N]) {
                let history = History::new(Cursor::new(input)).unwrap();
                let results: Vec<Result<Record, String>> = history
                    .iter()
                    .scan(false, |is_errored, result| {
                        if *is_errored {
                            None
                        } else {
                            *is_errored = result.is_err();
                            Some(result)
                        }
                    })
                    .collect();
                assert_eq!(results, expected.map(|r| r.map_err(String::from)));
            }
            check("", []);
            check("oops", [Err("malformed: \"oops\"")]);
            check("#", [Err("malformed: \"#\"")]);
            check("#1", [Err("malformed: \"#1\"")]);
            check("#1\n", [Err("malformed: \"\"")]);
            check("#1\n\n", [Ok(Record { entire: "#1\n\n", command: "" })]);
            check("#23\nfoo bar\n#456\nzab\n", [
                Ok(Record { entire: "#23\nfoo bar\n", command: "foo bar" }),
                Ok(Record { entire: "#456\nzab\n", command: "zab" }),
            ]);
            check("#7\nA\n#8\nB", [
                Ok(Record { entire: "#7\nA\n", command: "A" }),
                Err("malformed: \"B\""),
            ]);
            check("#7\nA\n#8\nB\n#9", [
                Ok(Record { entire: "#7\nA\n", command: "A" }),
                Err("malformed: \"B\"..."),
            ]);
            check("#7\nA\n#8\nB\n#9\n", [
                Ok(Record { entire: "#7\nA\n", command: "A" }),
                Ok(Record { entire: "#8\nB\n", command: "B" }),
                Err("malformed: \"\""),
            ]);
            check("#12345\n multi\nline \n ...\n", [Ok(Record {
                entire:  "#12345\n multi\nline \n ...\n",
                command: " multi\nline \n ...",
            })]);
        }
    }

    mod advance_past {
        pub fn timestamp(s: &str) -> Option<usize> {
            let mut opt = None;
            if s.starts_with('#') {
                if let Some(end) = s.find('\n') {
                    let range = 1 .. end;
                    if !range.is_empty() && s[range].chars().all(|c| c.is_ascii_digit()) {
                        let rest_index = end + 1;
                        opt = Some(rest_index);
                    }
                }
            }
            opt
        }

        pub fn command(s: &str, mut idx: usize) -> Option<usize> {
            let mut opt = None;
            while let Some(line_end) = s[idx ..].find('\n') {
                idx += line_end + 1;
                let rest = &s[idx ..];
                if rest.is_empty() || timestamp(rest).is_some() {
                    opt = Some(idx);
                    break;
                }
            }
            opt
        }

        #[cfg(test)]
        mod tests {
            #[test]
            fn timestamp() {
                fn check(s: &str, expected: Option<usize>) {
                    assert_eq!(super::timestamp(s), expected);
                }
                check("", None);
                check(" ", None);
                check("oops", None);
                check("#", None);
                check("#1", None);
                check("\n", None);
                check(" \n", None);
                check("oops\n", None);
                check("#\n", None);
                check("#1x2\n", None);
                check("#0\n", Some(3));
                check("#123\n", Some(5));
                check("#9876543210\n", Some(12));
            }

            #[test]
            fn command() {
                fn check(s: &str, cmd_start: usize, expected: Option<usize>) {
                    assert_eq!(super::command(s, cmd_start), expected);
                }
                check("", 0, None);
                check("#1\n", 3, None);
                check("#1\n\n", 3, Some(3 + 1));
                check("#1\nx\n", 3, Some(3 + 2));
                check("#1\na\n ", 3, None);
                check("#1\na\nb", 3, None);
                check("#1\n\n#0", 3, None);
                check("#1\n\n#0\n", 3, Some(3 + 1));
                check("#1\na\n#22", 3, None);
                check("#1\na\n#22\n", 3, Some(3 + 2));
                check("#321\n", 5, None);
                check("#321\n\n", 5, Some(5 + 1));
                check("#321\nx\n", 5, Some(5 + 2));
                check("#9876543210\nabc\n#123456789", 12, None);
                check("#9876543210\nabc\n#123456789\n", 12, Some(12 + 4));
                check("#9876\nabc  # comment\n#1234\n", 6, Some(6 + 15));
                check("#283472\nmulti\n line \n...\n#623370\n", 8, Some(8 + 17));
                check("#666666\n#666\n", 8, Some(8 + 5));
            }
        }
    }
}


mod pruned {
    use {crate::{Record, RegexSet},
         std::{collections::{hash_map::Entry, HashMap},
               io::{self, Write}}};

    pub struct Pruned<'l> {
        kept: Vec<Option<Record<'l>>>,
    }

    impl<'l> Pruned<'l> {
        pub fn new(records: impl IntoIterator<Item = Record<'l>>, ignores: RegexSet) -> Self {
            let mut kept = Vec::new();
            let mut seen = HashMap::new();
            let noticed_records =
                records.into_iter().filter(|record| !ignores.is_match(record.command));
            for record in noticed_records {
                let index = kept.len();
                kept.push(Some(record));
                match seen.entry(record.command) {
                    Entry::Occupied(mut entry) => {
                        let prior_index = entry.insert(index);
                        kept[prior_index] = None;
                    },
                    Entry::Vacant(entry) => {
                        entry.insert(index);
                    },
                }
            }
            Self { kept }
        }

        fn iter(&self) -> impl Iterator<Item = &Record<'l>> {
            self.kept.iter().filter_map(Option::as_ref)
        }

        pub fn dump(&self, out: &mut impl Write) -> io::Result<()> {
            for record in self.iter() {
                out.write_all(record.to_string().as_bytes())?;
            }
            out.flush()?;
            Ok(())
        }
    }
}


#[cfg(test)]
mod tests {
    use {super::*, std::io::Cursor};

    #[test]
    fn basic() {
        #[rustfmt::skip]
        const IGNORES: &str = "\
          ^no-longer( +--(cool|interesting))+$\n\
          \\bboring\\b\n\
        ";
        #[rustfmt::skip]
        const PREV_COMBINED: &str = "\
          #0\n\
          no-longer --interesting\n\
          #1\n\
          echo first\n\
          #22\n\
          #666\n\
          #333\n\
          cargo help\n\
        ";
        #[rustfmt::skip]
        const A_SESSION: &str = "\
          #4444\n\
          echo fourth\n\
          #55555\n\
          cargo help\n\
          #666666\n\
          #666\n\
          #7777777\n\
          boring\n\
          #88888888\n\
          for I in $(seq 5)  # multi-line\n\
          do\n\
            echo $I\n\
          done\n\
          #999999999\n\
          extra-boring --times=10\n\
          #0000000000\n\
          cat <<<'last'\n\
        ";
        #[rustfmt::skip]
        const EXPECTED: &str = "\
          #1\n\
          echo first\n\
          #4444\n\
          echo fourth\n\
          #55555\n\
          cargo help\n\
          #666666\n\
          #666\n\
          #88888888\n\
          for I in $(seq 5)  # multi-line\n\
          do\n\
            echo $I\n\
          done\n\
          #0000000000\n\
          cat <<<'last'\n\
        ";
        let input_files: [Cursor<&str>; 2] = [PREV_COMBINED, A_SESSION].map(Cursor::new);
        let ignores_file = Cursor::new(IGNORES);
        let mut output = Vec::new();

        combine_and_prune(input_files, Some(ignores_file), &mut output).unwrap();

        let output = String::from_utf8(output).unwrap();
        assert_eq!(output, EXPECTED);
    }
}
