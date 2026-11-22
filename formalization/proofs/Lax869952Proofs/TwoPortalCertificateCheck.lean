import Lax869952Proofs.TwoPortalCertificateData
import Mathlib.Tactic.IntervalCases

set_option warningAsError true

namespace Lax869952Proofs.TwoPortalCertificate

private def group : ℕ → Array (List Move)
  | 0 => moves0
  | 1 => moves1
  | 2 => moves2
  | 3 => moves3
  | 4 => moves4
  | 5 => moves5
  | 6 => moves6
  | 7 => moves7
  | 8 => moves8
  | 9 => moves9
  | 10 => moves10
  | 11 => moves11
  | 12 => moves12
  | 13 => moves13
  | 14 => moves14
  | 15 => moves15
  | _ => #[]

def certificate (o : Fin 256) : List Move :=
  (group (o.val / 16))[o.val % 16]!

private def checkGroup (g : ℕ) : Bool :=
  (List.finRange 16).all fun i => check (16 * g + i.val) (group g)[i.val]!

section
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000

private theorem check0 : checkGroup 0 = true := by decide
private theorem check1 : checkGroup 1 = true := by decide
private theorem check2 : checkGroup 2 = true := by decide
private theorem check3 : checkGroup 3 = true := by decide
private theorem check4 : checkGroup 4 = true := by decide
private theorem check5 : checkGroup 5 = true := by decide
private theorem check6 : checkGroup 6 = true := by decide
private theorem check7 : checkGroup 7 = true := by decide
private theorem check8 : checkGroup 8 = true := by decide
private theorem check9 : checkGroup 9 = true := by decide
private theorem check10 : checkGroup 10 = true := by decide
private theorem check11 : checkGroup 11 = true := by decide
private theorem check12 : checkGroup 12 = true := by decide
private theorem check13 : checkGroup 13 = true := by decide
private theorem check14 : checkGroup 14 = true := by decide
private theorem check15 : checkGroup 15 = true := by decide

end

theorem certificate_checked (o : Fin 256) : check o.val (certificate o) = true := by
  have group_checked (g : ℕ) (hg : g < 16) : checkGroup g = true := by
    interval_cases g
    · exact check0
    · exact check1
    · exact check2
    · exact check3
    · exact check4
    · exact check5
    · exact check6
    · exact check7
    · exact check8
    · exact check9
    · exact check10
    · exact check11
    · exact check12
    · exact check13
    · exact check14
    · exact check15
  let lo : Fin 16 := ⟨o.val % 16, Nat.mod_lt _ (by decide)⟩
  have hi : o.val / 16 < 16 := by omega
  have h := List.all_eq_true.mp (group_checked (o.val / 16) hi) lo (List.mem_finRange lo)
  have he : 16 * (o.val / 16) + lo.val = o.val := by
    dsimp [lo]
    omega
  change check (16 * (o.val / 16) + lo.val) (certificate o) = true at h
  rwa [he] at h

#print axioms certificate_checked

end Lax869952Proofs.TwoPortalCertificate
