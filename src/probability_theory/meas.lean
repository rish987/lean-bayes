import measure_theory.measure.measure_space
open measure_theory measure_theory.measure measurable_space

open measure_theory measurable_space

namespace probability_theory

section

variables {α : Type*} [measurable_space α] (μ : measure α)

section definitions

/-- Type class wrapper for measurable sets. -/
class meas (s : set α) : Prop :=
(meas : measurable_set s)

/-- Type class wrapper for measurable functions. -/
class fmeas [measurable_space α] {β : Type*} [measurable_space β] (f : α → β) : Prop :=
(fmeas : measurable f)

/-- Represents the notion that a conditional probability measure "exists" for a measure `μ`
and set `s` exactly when `s` is measurable with nonzero measure. -/
class cond_meas (s : set α) extends meas s : Prop :=
(meas_nz : μ s ≠ 0)

end definitions

-- TODO can this theorem be inferred automatically somehow?
lemma cond_meas_iff (s : set α) : cond_meas μ s ↔ μ s ≠ 0 ∧ measurable_set s :=
begin
  split,
  { intro hcms, exact ⟨hcms.meas_nz, hcms.meas⟩ },
  { rintro ⟨hnz, hm⟩, haveI := meas.mk hm, exact ⟨hnz⟩ }
end

lemma not_cond_meas_zero {s : set α} [hms : meas s] (h : ¬cond_meas μ s) : μ s = 0 :=
by simp [cond_meas_iff] at h; exact not_imp_not.mp h hms.meas

instance meas_inter_of_meas [measurable_space α] {s t : set α} [h1 : meas s] [h2 : meas t] :
  meas (s ∩ t) := ⟨measurable_set.inter h1.meas h2.meas⟩

-- TODO can I replace the below two instances with something like this?
--instance cond_meas_of_cond_meas_subset {s t : set α} [meas t]
--  [hcmi : cond_meas μ s] [hsub : inhabited (s ⊆ t)] :
--  cond_meas μ t := ⟨ne_bot_of_le_ne_bot hcmi.meas_nz (μ.mono hsub.default)⟩

instance cond_meas_of_cond_meas_inter₀ {s t : set α} [meas t] [hcmi : cond_meas μ (s ∩ t)] :
  cond_meas μ t := ⟨ne_bot_of_le_ne_bot hcmi.meas_nz (μ.mono (set.inter_subset_right _ _))⟩

instance cond_meas_of_cond_meas_inter₁ {s t : set α} [meas s] [hcmi : cond_meas μ (s ∩ t)] :
  cond_meas μ s := ⟨ne_bot_of_le_ne_bot hcmi.meas_nz (μ.mono (set.inter_subset_left _ _))⟩

end

lemma map_map' {α β γ : Type*} [measurable_space α] [measurable_space β] [measurable_space γ]
{g : β → γ} {f : α → β} [hg : fmeas g] [hf : fmeas f] (μ : measure α) :
  map g (map f μ) = map (g ∘ f) μ := map_map hg.fmeas hf.fmeas

lemma map_apply' {α : Type*} {β : Type*} [measurable_space α] [measurable_space β]
  {μ : measure α} {f : α → β} [hfm : fmeas f] (s : set β) [hms : meas s]
  : map f μ s = μ (f ⁻¹' s) := map_apply hfm.fmeas hms.meas

instance fmeas_pi_of {α : Type*} {δ : Type*} {π : δ → Type*}
  [measurable_space α] [Π (a : δ), measurable_space (π a)]
  {g : α → Π (a : δ), π a} [hmg : fmeas g] (a : δ) :
  fmeas (λ (x : α), g x a) := ⟨measurable_pi_iff.mp hmg.fmeas a⟩

instance fmeas_pi_from {α : Type*} {δ : Type*} {π : δ → Type*}
  [measurable_space α] [Π (a : δ), measurable_space (π a)]
  {g : α → Π (a : δ), π a} [hmg : ∀ (a : δ), fmeas (λ (x : α), g x a)] :
  fmeas g  := ⟨measurable_pi_iff.mpr (λ a, (hmg a).fmeas)⟩

instance meas_preimage_of_fmeas_meas
  {α : Type*} {β : Type*} [measurable_space α] [measurable_space β]
  {f : α → β} [hfm : fmeas f] (s : set β) [hms : meas s] :
  meas (f ⁻¹' s) := ⟨fmeas.fmeas hms.meas⟩

end probability_theory
