# Compact sweep backing-array ownership

This review is bound to the emitted files in `emitted-code.sha256` and uses
the pinned Lean consuming-write ABI. The invariant at the fold cursor is
one owning reference to each mutable bank and no reference to an earlier
state in the remaining rows or the event log.

- **Entry.** The compact builder extracts the initialized jump memory and
  releases the initialization result before entering `fromRoot`. `initial`
  retains that memory and allocates the slot, back-key, and label columns
  independently. Configuration and rank lookup only reference immutable
  objects. Dictionary keys are separate from the mutable slot array.
- **Row planning.** The fold moves its state into `stepPrepared`. The latter
  takes references to the tables and labels and moves the old state into
  `selectors`. Its read closures are temporary. `runPrepared` releases the
  selectors on the stopped branch or passes them to `active`. In the latter
  case the prefix search consumes its probe closure and the final node
  selection consumes the remaining selector reference. The returned
  measured record has a request and numeric counts. It retains no tables.
  Thus the references reserved for the writes are sole owners at install.
- **Installation.** A stopped row or reused key returns the original
  tables by ownership transfer. A fresh key consumes the table record.
  Its dictionary search reads the distinct immutable key array.
  `appendLeafWords` reads the previous words before it consumes the jump
  bank. It threads the returned bank through three field writes and the
  header write. The result wrapper is released before the consuming header
  write. The slot and reverse-key writes consume their independent arrays.
  Array reads yield scalar words or key values that cannot point back to a
  bank. Bounds for the successful allocation follow from Lean's
  `appendLeafWords_spec` and `stepPrepared_exactCapacity`.
- **Handoff.** The label update consumes the reserved label bank. The
  fold extracts the next state, releases the completed row result and
  advances at its tail-loop jump. The event contains just the head, node,
  allocation flag, parent and optional key, so past events cannot retain
  previous banks. The array sizes stay the same during successful writes.

Lean's exact trace counts one label write per successful row and six
backing-array writes per fresh key. The fresh branch also advances the
next-slot scalar counter. The C review checks the unique-owner invariant
for these writes and supports the constant-cost array update premise
in the sweep's source work model. This review covers the row-update path.
Input preparation, the final finish, and full scalar/control coverage
require their own arguments.
