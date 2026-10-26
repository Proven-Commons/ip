import Ip

namespace Ip

/-- Every IPv4 value fits in 32 bits. -/
theorem IPv4.toNat_lt (a : IPv4) : a.toNat < 4294967296 := by
  unfold IPv4.toNat
  have h0 := a.b0_lt
  have h1 := a.b1_lt
  have h2 := a.b2_lt
  have h3 := a.b3_lt
  omega

/-- Every IPv6 value fits in 128 bits. -/
theorem IPv6.toNat_lt (a : IPv6) : a.toNat < 2 ^ 128 := by
  unfold IPv6.toNat
  have h0 := a.g0_lt
  have h1 := a.g1_lt
  have h2 := a.g2_lt
  have h3 := a.g3_lt
  have h4 := a.g4_lt
  have h5 := a.g5_lt
  have h6 := a.g6_lt
  have h7 := a.g7_lt
  omega

/-- A parsed octet is below 256. -/
theorem parseOctet_lt {cs : List Char} {n : Nat} (h : parseOctet cs = some n) :
    n < 256 := by
  unfold parseOctet at h
  by_cases hc : (!noLeadingZero cs) = true
  · rw [if_pos hc] at h
    simp at h
  · rw [if_neg hc] at h
    cases hn : parseDecNat cs with
    | none => rw [hn] at h; simp at h
    | some m =>
      simp only [hn] at h
      by_cases hm : m < 256
      · rw [if_pos hm] at h
        exact Option.some.inj h ▸ hm
      · rw [if_neg hm] at h
        simp at h

/-- A successful IPv4 parse consumes exactly four dot-separated parts. -/
theorem parseIPv4Parts_length {parts : List (List Char)} {a : IPv4}
    (h : parseIPv4Parts parts = some a) : parts.length = 4 := by
  cases parts with
  | nil => simp [parseIPv4Parts] at h
  | cons s0 rest =>
    cases rest with
    | nil => simp [parseIPv4Parts] at h
    | cons s1 rest =>
      cases rest with
      | nil => simp [parseIPv4Parts] at h
      | cons s2 rest =>
        cases rest with
        | nil => simp [parseIPv4Parts] at h
        | cons s3 rest =>
          cases rest with
          | nil => rfl
          | cons _ _ => simp [parseIPv4Parts] at h

/-- A successful IPv4 parse splits into exactly four parts. -/
theorem parseIPv4_length {s : String} {a : IPv4}
    (h : parseIPv4 s = some a) : (splitChar '.' s.toList).length = 4 :=
  parseIPv4Parts_length h

/-- What a successful prefix build gives: the parts, the bound. -/
theorem mkPrefix_spec {a : IPAddr} {len : Nat} {p : Prefix}
    (h : mkPrefix a len = some p) :
    p.addr = a ∧ p.len = len ∧ len ≤ a.bits := by
  unfold mkPrefix at h
  by_cases hc : len ≤ a.bits
  · rw [dif_pos hc] at h
    have hp : (⟨a, len, hc⟩ : Prefix) = p := Option.some.inj h
    refine ⟨?_, ?_, hc⟩
    · rw [← hp]
    · rw [← hp]
  · rw [dif_neg hc] at h
    simp at h

/-- A successful prefix parse respects the address size. -/
theorem parsePrefixParts_len_le {parts : List (List Char)} {p : Prefix}
    (h : parsePrefixParts parts = some p) : p.len ≤ p.addr.bits := by
  cases parts with
  | nil => simp [parsePrefixParts] at h
  | cons a rest =>
    cases rest with
    | nil => simp [parsePrefixParts] at h
    | cons l rest =>
      cases rest with
      | nil =>
        simp only [parsePrefixParts] at h
        cases hlen : parsePrefixLen l with
        | none => rw [hlen] at h; simp at h
        | some len =>
          rw [hlen] at h
          cases haddr : parseAddrList a with
          | none => rw [haddr] at h; simp at h
          | some addr =>
            rw [haddr] at h
            dsimp only at h
            obtain ⟨h1, h2, h3⟩ := mkPrefix_spec h
            rw [h2, h1]
            exact h3
      | cons _ _ => simp [parsePrefixParts] at h

/-- A successful prefix parse respects the address size. -/
theorem parsePrefix_len_le {s : String} {p : Prefix}
    (h : parsePrefix s = some p) : p.len ≤ p.addr.bits :=
  parsePrefixParts_len_le h

/-- Membership for IPv4 is equality of the shifted values. -/
theorem inPrefix_v4 (x y : IPv4) (len : Nat) :
    inPrefix (IPAddr.v4 x) (IPAddr.v4 y) len =
      ((x.toNat >>> (32 - len)) == (y.toNat >>> (32 - len))) :=
  rfl

/-- Membership for IPv6 is equality of the shifted values. -/
theorem inPrefix_v6 (x y : IPv6) (len : Nat) :
    inPrefix (IPAddr.v6 x) (IPAddr.v6 y) len =
      ((x.toNat >>> (128 - len)) == (y.toNat >>> (128 - len))) :=
  rfl

/-- Addresses of different versions never match. -/
theorem inPrefix_mixed (x : IPv4) (y : IPv6) (len : Nat) :
    inPrefix (IPAddr.v4 x) (IPAddr.v6 y) len = false :=
  rfl

/-- Shifting right further preserves equality of shifted values. -/
theorem shiftRight_mono {x y k k' : Nat} (h : k ≤ k')
    (e : x >>> k = y >>> k) : x >>> k' = y >>> k' := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow] at *
  have hk : k' = k + (k' - k) := (Nat.add_sub_cancel' h).symm
  rw [hk, Nat.pow_add, ← Nat.div_div_eq_div_mul, e, Nat.div_div_eq_div_mul]

/--
  Membership is preserved when a prefix widens: matching on more
  bits implies matching on fewer. Here `len' ≤ len` means the
  second prefix is wider (less specific).
-/
theorem inPrefix_widen_v4 {x y : IPv4} {len len' : Nat}
    (hle : len' ≤ len) (hlen : len ≤ 32)
    (h : inPrefix (IPAddr.v4 x) (IPAddr.v4 y) len = true) :
    inPrefix (IPAddr.v4 x) (IPAddr.v4 y) len' = true := by
  rw [inPrefix_v4] at h ⊢
  rw [beq_iff_eq] at h ⊢
  exact shiftRight_mono (Nat.sub_le_sub_left hle 32) h

/-- Membership is preserved when an IPv6 prefix widens. -/
theorem inPrefix_widen_v6 {x y : IPv6} {len len' : Nat}
    (hle : len' ≤ len) (hlen : len ≤ 128)
    (h : inPrefix (IPAddr.v6 x) (IPAddr.v6 y) len = true) :
    inPrefix (IPAddr.v6 x) (IPAddr.v6 y) len' = true := by
  rw [inPrefix_v6] at h ⊢
  rw [beq_iff_eq] at h ⊢
  exact shiftRight_mono (Nat.sub_le_sub_left hle 128) h

/-- Parsing is deterministic: it is a function, so the same input
gives the same result. Stated for each entry point. -/
theorem parseIPv4_deterministic (s : String) : parseIPv4 s = parseIPv4 s := rfl

theorem parseIPv6_deterministic (s : String) : parseIPv6 s = parseIPv6 s := rfl

theorem parsePrefix_deterministic (s : String) : parsePrefix s = parsePrefix s := rfl

/-- Acceptance: ordinary addresses parse. -/
theorem accept_ipv4 : (parseIPv4 "192.168.0.1").isSome = true := by decide

theorem accept_ipv4_loopback : (parseIPv4 "127.0.0.1").isSome = true := by decide

theorem accept_ipv6_full :
    (parseIPv6 "2001:0db8:85a3:0000:0000:8a2e:0370:7334").isSome = true := by decide

theorem accept_ipv6_compressed : (parseIPv6 "2001:db8::1").isSome = true := by decide

theorem accept_ipv6_loopback : (parseIPv6 "::1").isSome = true := by decide

theorem accept_ipv6_unspecified : (parseIPv6 "::").isSome = true := by decide

theorem accept_ipv6_embedded : (parseIPv6 "::ffff:192.0.2.1").isSome = true := by decide

theorem accept_prefix_v4 : (parsePrefix "10.0.0.0/8").isSome = true := by decide

theorem accept_prefix_v6 : (parsePrefix "2001:db8::/32").isSome = true := by decide

/-- Rejection: an extra part is never accepted. -/
theorem reject_ipv4_extra_part : parseIPv4 "1.2.3.4.5" = none := by decide

theorem reject_ipv4_extra_part_v6 : parseIPv6 "1:2:3:4:5:6:7:8:9" = none := by decide

/-- Rejection: an out-of-range octet is never accepted. -/
theorem reject_ipv4_octet_range : parseIPv4 "256.0.0.1" = none := by decide

theorem reject_ipv4_octet_empty : parseIPv4 "1.2.3." = none := by decide

/-- Rejection: a leading zero octet is never accepted. -/
theorem reject_ipv4_leading_zero : parseIPv4 "01.2.3.4" = none := by decide

/-- Rejection: a trailing space is never accepted. -/
theorem reject_ipv4_trailing_space : parseIPv4 "1.2.3.4 " = none := by decide

/-- Rejection: too few parts are never accepted. -/
theorem reject_ipv4_too_few : parseIPv4 "1.2.3" = none := by decide

/-- Rejection: a second compression is never accepted. -/
theorem reject_ipv6_double_compress : parseIPv6 "1::2::3" = none := by decide

/-- Rejection: too few groups without compression are never accepted. -/
theorem reject_ipv6_too_few : parseIPv6 "1:2:3:4:5:6:7" = none := by decide

/-- Rejection: a bad hex group is never accepted. -/
theorem reject_ipv6_bad_hex : parseIPv6 "gggg::1" = none := by decide

/-- Rejection: a group over four digits is never accepted. -/
theorem reject_ipv6_group_too_long : parseIPv6 "12345::1" = none := by decide

/-- Rejection: an empty group outside compression is never accepted. -/
theorem reject_ipv6_empty_group : parseIPv6 "1:2:3:4:5:6:7:" = none := by decide

/-- Rejection: an IPv4 tail away from the end is never accepted. -/
theorem reject_ipv6_mid_embedded : parseIPv6 "1.2.3.4::5" = none := by decide

/-- Rejection: a prefix length past the address size is never accepted. -/
theorem reject_prefix_v4_too_long : parsePrefix "1.2.3.4/33" = none := by decide

theorem reject_prefix_v6_too_long : parsePrefix "2001:db8::1/129" = none := by decide

/-- Rejection: a missing or malformed length is never accepted. -/
theorem reject_prefix_empty_len : parsePrefix "1.2.3.4/" = none := by decide

theorem reject_prefix_two_slashes : parsePrefix "1.2.3.4/24/5" = none := by decide

theorem reject_prefix_negative : parsePrefix "1.2.3.4/-1" = none := by decide

theorem reject_prefix_leading_zero : parsePrefix "1.2.3.4/024" = none := by decide

end Ip
