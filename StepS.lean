
import UPT.Basic
namespace UPT

theorem stepS_le_succ (n : Nat) : stepS n ≤ n+1 := by
  unfold stepS; omega

theorem same_bound_S (n : Nat) : stepS n ≤ n+3 := by
  have h := stepS_le_succ n; omega
