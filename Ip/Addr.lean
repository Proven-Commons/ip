/-
  Address types for the IP printer.

  An IPv4 address is four bytes. An IPv6 address is eight 16-bit groups.
  Each field carries its bound as a proof, so a value of these types is
  a valid address by construction. The printer never sees an out-of-range
  field.
-/

/-- An IPv4 address: four bytes, each below 256. -/
structure IPv4 where
  b0 : Nat
  b0_lt : b0 < 256
  b1 : Nat
  b1_lt : b1 < 256
  b2 : Nat
  b2_lt : b2 < 256
  b3 : Nat
  b3_lt : b3 < 256
deriving DecidableEq, Repr

/-- An IPv6 address: eight groups, each below 65536. -/
structure IPv6 where
  g0 : Nat
  g0_lt : g0 < 65536
  g1 : Nat
  g1_lt : g1 < 65536
  g2 : Nat
  g2_lt : g2 < 65536
  g3 : Nat
  g3_lt : g3 < 65536
  g4 : Nat
  g4_lt : g4 < 65536
  g5 : Nat
  g5_lt : g5 < 65536
  g6 : Nat
  g6_lt : g6 < 65536
  g7 : Nat
  g7_lt : g7 < 65536
deriving DecidableEq, Repr

/-- The eight groups of an IPv6 address as a list, in order. -/
def IPv6.groups (a : IPv6) : List Nat :=
  [a.g0, a.g1, a.g2, a.g3, a.g4, a.g5, a.g6, a.g7]

/-- The four bytes of an IPv4 address as a list, in order. -/
def IPv4.bytes (a : IPv4) : List Nat :=
  [a.b0, a.b1, a.b2, a.b3]
