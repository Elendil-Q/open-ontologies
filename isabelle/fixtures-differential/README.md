# `fixtures-differential/` — where the two kernels part company, and where they do not

Committed bytes for `tests/cross_kernel_differential_test.rs`. Two kinds of file.

## The divergences

Certificates that `lean/.lake/build/bin/oo-horn` and `isabelle/build/oo-horn-isabelle`
judge **differently**. They are committed so the result is reproducible from the
repository rather than from a generator, and neither checker was adjusted to make them
agree.

| files | what it is | Lean | Isabelle |
|---|---|---|---|
| `varname_rules.tsv`, `varname_asserted.tsv`, `varname_unbound_cert.tsv` | **D2a.** The binding omits `s`; the graph's subject is the bare term `s`, spelled exactly like the rule's variable. Lean's `substOf` sends an unbound variable to its own name, so the step checks. | accepts | rejects, `binding_incomplete` |
| `varname_bound_cert.tsv` | the control for D2a: bind `s` as well and both accept. Without it the divergence could be about anything in those three files. | accepts | accepts |
| `unsafehead_rules.tsv`, `unsafehead_asserted.tsv`, `unsafehead_cert.tsv` | **D2b**, the sharp form. The rule's head carries `?z`, which its body never binds, and the certificate omits `z`. Lean accepts a conclusion whose object is the bare term `z` — not an IRI, not a blank node, not a literal — minted out of a variable's name. | accepts | rejects, `binding_incomplete` |
| `d2c_fuzzfound_rules.tsv`, `d2c_fuzzfound_asserted.tsv`, `d2c_fuzzfound_cert.tsv` | **D2c**, and nobody designed it. The seeded fuzzer changed one field of `probe_degen2_rules.tsv`: `?o` became a bare `?`, which both parsers read as a variable whose NAME IS THE EMPTY STRING. The graph's object is an empty field, so Lean's default sends `""` to `""` and the step checks. The hole is reachable by a typo. | accepts | rejects, `binding_incomplete` |

**D1** needs no file here: it is `../fixtures-added/bad_dup_key.tsv`, which binds `x` twice.
Isabelle rejects a repeated binding key as malformed; Lean resolves it with `List.lookup`,
which is first-wins, and accepts with the ABSOLUTE verdict.

All three have one root cause. Isabelle's `check_step` validates the binding list as a
data structure — `distinct (map fst b)`, then `binding_covers b r` — before instantiating
anything. Lean's `substOf` is `fun v => (List.lookup v l).getD v`: it turns any binding
list into a total function with a silent default and never inspects it.

Neither checker is unsound. Lean's acceptances hold in Lean's own theorem, because
`EntailsR` quantifies over every total substitution and the one Lean used is real;
Isabelle's rejections are false alarms. What is wrong is the FORMAT, which does not say
whether a binding must have distinct keys or must cover the cited rule's variables. Until
it does, a certificate's validity depends on which verified checker reads it.

## The probes

`probe_<name>_{rules,asserted,cert}.tsv`. Corners of the term format that **no generated
certificate reaches**, because the engine writes IRIs and every RDF fixture in this
repository is ASCII. Both kernels agree on all of them; the expected answer is written
down in `the_untested_corners_of_the_term_format_agree`, because agreement on the WRONG
answer is the one failure a differential cannot see by itself.

| probe | what it exercises | expected |
|---|---|---|
| `utf8` | non-ASCII IRIs (`café`, CJK, an emoji) in rule, graph and certificate | accepted |
| `utf8bad` | one byte of a non-ASCII IRI altered in the certificate | rejected |
| `literals` | a language-tagged literal and a datatyped literal | accepted |
| `litdt` | `"01"^^xsd:integer` standing in for `"1"^^xsd:integer` — one value, two terms | rejected |
| `bnode` | blank node labels in subject and object | accepted |
| `degen` | the degenerate spellings `<>` and `_:` | accepted |
| `degen2` | a bare `<` and an empty field, as terms | accepted |
| `inject` | `http://ex.org/a` without its brackets, against `<http://ex.org/a>` with them | rejected |
| `emptybody` | a rule with an empty body, cited with no premises | accepted |
| `repeated` | a rule whose body repeats one atom, cited twice | accepted |
| `extrabind` | a binding for a variable the rule never mentions | accepted |
| `qmarkkey` | binding keys written WITH the leading `?` | rejected |
| `emptyall` | an empty rule table and an empty certificate | accepted |
| `emptyrules` | an empty rule table and a step citing rule 0 | rejected |
| `emptygraph` | an empty graph and a rule with an empty body | accepted |
| `allempty` | all three files empty | accepted |
| `duprow` | the built-in table with one row duplicated AFTER the cited index | accepted, relativised verdict |
| `trailtab` | a trailing tab on every certificate line | exit 2 |
| `crlf` | CRLF endings, so every last field carries a stray carriage return | rejected |
| `blank` | blank lines at the start and end of all three files | accepted |
| `nonl` | no trailing newline anywhere | accepted |
| `hugeidx` | a rule index of 200 digits | rejected |

The expected answer is an EXIT CODE, not a bit, because 2 is a third answer: a checker
that quietly turned an unparseable file into a rejection would still look like agreement
on the accept/reject bit alone.

`utf8` settles DECISION M38's open worry: the fixtures being pure ASCII is "exactly the
circumstance in which a `String.literal` implementation would stay silent", and the
verified core is over `string = char list`, so the bytes reach the theorem unchanged.
`litdt` settles M1's scope note. `inject` settles the injectivity that D-PARSE-2 needs for
bracket-stripping to be invisible to the accept/reject bit.

These also join the corpus as base cases, so they are mutated and fuzzed like everything
else rather than only being checked once.
