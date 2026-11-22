import TreeConjecture.HexagonData

set_option warningAsError true

namespace TreeConjecture.CycleCertificate.Cycle6

private theorem head_values : ∀ a : Fin 4, a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem cert0_head0 :
    checkPathHead cert0.2 1 1 0 = true := by rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem cert0_head1 :
    checkPathHead cert0.2 1 1 1 = true := by rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem cert0_head2 :
    checkPathHead cert0.2 1 1 2 = true := by rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem cert0_head3 :
    checkPathHead cert0.2 1 1 3 = true := by rfl

theorem checked0 : Checks cert0.1 cert0.2 1 1 := by
  apply checks_of_checkPathHeads (by decide) (by decide)
  intro head
  rcases head_values head with rfl | rfl | rfl | rfl
  · exact cert0_head0
  · exact cert0_head1
  · exact cert0_head2
  · exact cert0_head3

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem cert1_head0 :
    checkPathHead cert1.2 1 1 0 = true := by rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem cert1_head1 :
    checkPathHead cert1.2 1 1 1 = true := by rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem cert1_head2 :
    checkPathHead cert1.2 1 1 2 = true := by rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem cert1_head3 :
    checkPathHead cert1.2 1 1 3 = true := by rfl

theorem checked1 : Checks cert1.1 cert1.2 1 1 := by
  apply checks_of_checkPathHeads (by decide) (by decide)
  intro head
  rcases head_values head with rfl | rfl | rfl | rfl
  · exact cert1_head0
  · exact cert1_head1
  · exact cert1_head2
  · exact cert1_head3

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem cert2_head0 :
    checkPathHead cert2.2 1 1 0 = true := by rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem cert2_head1 :
    checkPathHead cert2.2 1 1 1 = true := by rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem cert2_head2 :
    checkPathHead cert2.2 1 1 2 = true := by rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem cert2_head3 :
    checkPathHead cert2.2 1 1 3 = true := by rfl

theorem checked2 : Checks cert2.1 cert2.2 1 1 := by
  apply checks_of_checkPathHeads (by decide) (by decide)
  intro head
  rcases head_values head with rfl | rfl | rfl | rfl
  · exact cert2_head0
  · exact cert2_head1
  · exact cert2_head2
  · exact cert2_head3

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem cert3_head0 :
    checkPathHead cert3.2 1 1 0 = true := by rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem cert3_head1 :
    checkPathHead cert3.2 1 1 1 = true := by rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem cert3_head2 :
    checkPathHead cert3.2 1 1 2 = true := by rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem cert3_head3 :
    checkPathHead cert3.2 1 1 3 = true := by rfl

theorem checked3 : Checks cert3.1 cert3.2 1 1 := by
  apply checks_of_checkPathHeads (by decide) (by decide)
  intro head
  rcases head_values head with rfl | rfl | rfl | rfl
  · exact cert3_head0
  · exact cert3_head1
  · exact cert3_head2
  · exact cert3_head3

end TreeConjecture.CycleCertificate.Cycle6
