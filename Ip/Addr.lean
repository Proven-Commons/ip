/-
  Address types for the IP parser.

  An IPv4 address is four bytes. An IPv6 address is eight 16-bit groups.
  Each field carries its bound as a proof, so a value of these types is
  a valid address by construction. The parser never builds an
  out-of-range field.

  A prefix is an address plus a length, with a proof that the length
  does not exceed the address size (32 for IPv4, 128 for IPv6).
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

/-- The numeric value of an IPv4 address, big-endian. -/
def IPv4.toNat (a : IPv4) : Nat :=
  a.b0 * 16777216 + a.b1 * 65536 + a.b2 * 256 + a.b3

/-- The numeric value of an IPv6 address, big-endian. -/
def IPv6.toNat (a : IPv6) : Nat :=
  a.g0 * 5192296858534827628530496329220096 +
  a.g1 * 79228162514264337593543950336 +
  a.g2 * 1208925819614629174706176 +
  a.g3 * 18446744073709551616 +
  a.g4 * 281474976710656 +
  a.g5 * 4294967296 +
  a.g6 * 65536 +
  a.g7

/-- An IP address, either version. -/
inductive IPAddr where
  | v4 : IPv4 → IPAddr
  | v6 : IPv6 → IPAddr
deriving DecidableEq, Repr

/-- The address size in bits: 32 for IPv4, 128 for IPv6. -/
def IPAddr.bits : IPAddr → Nat
  | v4 _ => 32
  | v6 _ => 128

/-- The numeric value of an address. -/
def IPAddr.toNat : IPAddr → Nat
  | v4 a => a.toNat
  | v6 a => a.toNat

/-- A prefix: an address plus a length that does not exceed the size. -/
structure Prefix where
  addr : IPAddr
  len : Nat
  len_le : len ≤ addr.bits
deriving DecidableEq, Repr

/--
  Membership: an address is inside a prefix exactly when its top
  `len` bits match the prefix address's top `len` bits. Comparing
  the values shifted right by the host-bit count does exactly that.
  Addresses of different versions never match.
-/
def inPrefix (a p : IPAddr) (len : Nat) : Bool :=
  match a, p with
  | IPAddr.v4 x, IPAddr.v4 y => (x.toNat >>> (32 - len)) == (y.toNat >>> (32 - len))
  | IPAddr.v6 x, IPAddr.v6 y => (x.toNat >>> (128 - len)) == (y.toNat >>> (128 - len))
  | _, _ => false
