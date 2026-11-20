# Construction source costs and storage

The checked target is the dense-order packed constructor for flat quotients
in Paper B v1.3, Lemma 3.2. The v1.3 Markdown SHA-256 is
`86098c578c3297fc7952aa357bec9c0d80b9c6e854ce117622561cda7c276808`.
The phase lemmas cover the populated branch with at least three vertices.
The existing small-quotient module supplies the semantics of the root-only
case.

The preparation charge is exactly `16*n_H + 10*m_H` sites. This includes
the map accumulator's reversal and the stamp read and possible stamp write
and list output on each deduplication visit. The stamp writes and list
outputs are charged on both branches as an upper allowance.

The scan control meter charges the list and predicate-result tests, and
allows both counter additions for each visited cell. The search control
meter charges the fuel and interval tests, midpoint arithmetic, fuel
decrement, predicate-result branch and four counter additions on the
selected return. The terminal allowance covers both exit branches. The
symbolic meter matches the source counters. The generated `ForestHead.c`
replaces division by two with a right shift.

The emitted C hashes bind the following ownership checks to the pinned
compiler. In each mutable loop the array starts freshly allocated and the
next iteration receives the consuming write's returned array.

- `KahnDecreasing.inverseRanks` starts with a fresh rank column and passes
  one state to `fillRanks`. `writeRank` borrows only from the input order.
  Its returned record carries only the updated array and counters.
- `EX51.groupMap` initializes the scatter array once. The borrowed bucket
  read supplies a list cell and neither that cell nor the key or emit
  closure retains the backing array. `finish` receives the scatter result,
  reverses one bucket at a time and moves the updated array to the next
  iteration.
- `ForestIncomingPrep.sources` reads immutable labelled row cells and
  writes the mapped row into an independent array. Its map loop reverses
  the accumulator once.
- `ForestIncoming.run` allocates separate stamp and output banks. The scan
  consumes and returns its stamp bank. The row and visit count carry no
  reference to either bank, and the scan result wrapper is released before
  the next outer iteration.

The new bounds are `3584*(n_H+m_H)*L^2` for the selected work charges and
`128*(n_H+m_H)` for the combined preparation, reached sweep-boundary and
finish reserves. The older dictionary and active-probe receipts cover
their named local cursors. The full Lemma 3.2 certificate still needs a
word-RAM refinement from these charges to all construction operations and
all live allocations. In particular the boundary theorem does not
describe the execution between the finish and serialization checkpoints.
