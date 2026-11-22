import TreeConjecture.HeptagonData

set_option warningAsError true

namespace TreeConjecture.CycleCertificate.Cycle7

private theorem head_values : ∀ a : Fin 4, a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem cert5_head0 :
    checkPathHead cert5.2 1 1 0 = true := by rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem cert5_head1 :
    checkPathHead cert5.2 1 1 1 = true := by rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem cert5_head2 :
    checkPathHead cert5.2 1 1 2 = true := by rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem cert5_head3 :
    checkPathHead cert5.2 1 1 3 = true := by rfl

theorem checked5 : Checks cert5.1 cert5.2 1 1 := by
  apply checks_of_checkPathHeads (by decide) (by decide)
  intro head
  rcases head_values head with rfl | rfl | rfl | rfl
  · exact cert5_head0
  · exact cert5_head1
  · exact cert5_head2
  · exact cert5_head3

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem cert6_head0 :
    checkPathHead cert6.2 1 1 0 = true := by rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem cert6_head1 :
    checkPathHead cert6.2 1 1 1 = true := by rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem cert6_head2 :
    checkPathHead cert6.2 1 1 2 = true := by rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem cert6_head3 :
    checkPathHead cert6.2 1 1 3 = true := by rfl

theorem checked6 : Checks cert6.1 cert6.2 1 1 := by
  apply checks_of_checkPathHeads (by decide) (by decide)
  intro head
  rcases head_values head with rfl | rfl | rfl | rfl
  · exact cert6_head0
  · exact cert6_head1
  · exact cert6_head2
  · exact cert6_head3

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem cert7_head0 :
    checkPathHead cert7.2 1 1 0 = true := by rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem cert7_head1 :
    checkPathHead cert7.2 1 1 1 = true := by rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem cert7_head2 :
    checkPathHead cert7.2 1 1 2 = true := by rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem cert7_head3 :
    checkPathHead cert7.2 1 1 3 = true := by rfl

theorem checked7 : Checks cert7.1 cert7.2 1 1 := by
  apply checks_of_checkPathHeads (by decide) (by decide)
  intro head
  rcases head_values head with rfl | rfl | rfl | rfl
  · exact cert7_head0
  · exact cert7_head1
  · exact cert7_head2
  · exact cert7_head3

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem cert8_head0 :
    checkPathHead cert8.2 1 1 0 = true := by rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem cert8_head1 :
    checkPathHead cert8.2 1 1 1 = true := by rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem cert8_head2 :
    checkPathHead cert8.2 1 1 2 = true := by rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem cert8_head3 :
    checkPathHead cert8.2 1 1 3 = true := by rfl

theorem checked8 : Checks cert8.1 cert8.2 1 1 := by
  apply checks_of_checkPathHeads (by decide) (by decide)
  intro head
  rcases head_values head with rfl | rfl | rfl | rfl
  · exact cert8_head0
  · exact cert8_head1
  · exact cert8_head2
  · exact cert8_head3

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem cert9_head0 :
    checkPathHead cert9.2 1 1 0 = true := by rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem cert9_head1 :
    checkPathHead cert9.2 1 1 1 = true := by rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem cert9_head2 :
    checkPathHead cert9.2 1 1 2 = true := by rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem cert9_head3 :
    checkPathHead cert9.2 1 1 3 = true := by rfl

theorem checked9 : Checks cert9.1 cert9.2 1 1 := by
  apply checks_of_checkPathHeads (by decide) (by decide)
  intro head
  rcases head_values head with rfl | rfl | rfl | rfl
  · exact cert9_head0
  · exact cert9_head1
  · exact cert9_head2
  · exact cert9_head3

end TreeConjecture.CycleCertificate.Cycle7
