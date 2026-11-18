# Final arc of a surviving path

Gemini 4 Carbon Medium supplied `AvoidPath.eq_or_exists_last_arc` through the research relay. It proves that a surviving path either has equal endpoints or has a final arc whose tail is reachable from the source by a surviving prefix. The first-proper-loss proof uses this decomposition to identify an entering predecessor distinct from the deleted vertex. [Lean source](../../release-core/PaperB/Spec.lean)

Carbon saved the declaration in `0001.md` and sealed the report with `COMPLETE`. The declaration was available before the transport returned. The proof body was integrated verbatim. The scoped `PaperB.Spec` build passed on Lean 4.35.0-rc3, and Lean reported no axiom dependencies for the declaration. [Elaborated declaration and axiom check](build.txt) · [Relay and verification record](verification.json)
