# EX6.1 guarded-decoder witness fidelity

The Boolean truth predicate is defined recursively on the supplied
acyclic decoder rank. The path equivalence handles every gate kind:
OR, guard, labelled terminal or constant zero. It allows any number
of terminal vertices with the same label. The guarded path keeps
each guard disjoint from the activating set.

Under the healthy-zero reference singleton and the allowed forced set
(Q), any admissible witness has a path ending at a non-reference
label (i). The same path survives when the input is reduced to
(Q cup \{i\}). Forced guard deletion plus the candidate's remaining
guard failures yields exactly the same path predicate, including the
case where the source guard is removed. The list realization and
cost bounds are separate EX6.2 obligations.
