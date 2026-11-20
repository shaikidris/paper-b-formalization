# Dictionary sort backing-array ownership

This audit applies to the generated C of the pinned Lean build identified in
`emitted-code.sha256`. It uses Lean's consuming array-write convention.
`lean_array_fset` delegates to the exclusive-array check before the write.
Array reads borrow the array or retain just the loaded value. Keys contain
two naturals, so retaining a key cannot retain its backing array.

1. **Setup.** `initialBanksReserved` produces the bank through `Array.ofFn`.
   It reads keys from an immutable input array and writes to a distinct
   destination with capacity for the full index range. The closure captures
   the input. The destination is private to the generator. The empty
   bank causes no writes. `packedKeys` transfers the destination to
   `FixedBank.runPacked`.
2. **Recursive sort.** `runPacked` transfers the incoming bank to
   `runSpan`. On the split branch, `runSpan` moves the bank to the
   left call. It reads the returned bank field, acquires that reference,
   and releases the result wrapper before passing the bank to the right
   call. It does the same with the right result before invoking the
   merge. Suspended frames retain spans and counts. Result wrappers
   are newly returned records and are consumed or reused.
3. **Leaf and merge.** The nonempty copying leaf reads the key and
   uses its sole bank reference at `lean_array_fset`. The merge's
   loop borrows the bank to read source keys. Each of its five write
   branches consumes the current bank at `lean_array_fset`, assigns
   the returned bank to the loop variable and jumps back to the loop.
   The terminating branches move the bank into their returned record.
   The source-disjointness and write address bounds are checked in Lean.
4. **Handoff.** The final slice extraction is a bounded linear
   materialization that the existing dictionary work trace charges.

Thus, starting with a private bank, both recursive children and the
merge preserve its unique ownership on the audited sort path. No older
bank is needed by a later write. Lean checks the logical replacement of
the initializer and the sort's word-access trace. This C ownership
argument is a source audit. It covers the dictionary sort and does not
certify the rest of the constructor or the compiler.
