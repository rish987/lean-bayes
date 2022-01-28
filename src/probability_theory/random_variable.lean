import measure_theory.measure.measure_space

noncomputable theory

open measure_theory measure_theory.measure measurable_space

namespace measurable_space

section

variables {α δ γ : Type*} {π : δ → Type*} [measurable_space α]
  [Π a, measurable_space (π a)] [measurable_space γ]

lemma measurable_pi_subtype (s : set δ) :
  measurable (λ (g : Π (i : δ), π i) (i : s), g i) :=
begin
  rw measurable_pi_iff,
  intro a,
  rw measurable_iff_comap_le,
  -- FIXME why can't the lambda below be inferred?
  exact le_supr (λ a, (_inst_2 a).comap (λ (b : Π a, π a), b a)) _,
end

end

end measurable_space

namespace probability_theory

section

variables {α : Type*} [m : measurable_space α] (μ : measure α) {ι: Type*}
  {β : ι → Type*} [hmsb : (Π i : ι, measurable_space (β i))] (f : Π i : ι, α → (β i))

include hmsb

section definitions

def joint : measure (Π i : ι, β i) := map (λ a i, f i a) μ

def marginal (mv : set ι) : measure (Π i : mv, β i) :=
  joint μ (λ (i : mv) a, f i a)

end definitions

variable (hm : ∀ i : ι, measurable (f i))
include hm

lemma marginalization_aux (mv : set ι) :
  marginal μ f mv = map (λ (g : Π i, β i) (i : mv), g i) (joint μ f) :=
by rw [joint, map_map _ (measurable_pi_iff.mpr hm), function.comp];
  try {refl}; exact measurable_space.measurable_pi_subtype _

theorem marginalization (hm : ∀ i : ι, measurable (f i)) (mv : set ι) 
  (s : set (Π i : mv, β i)) (hms : measurable_set s) :
  marginal μ f mv s = joint μ f ((λ (g : Π i, β i) (i : mv), g i) ⁻¹' s) :=
by rw [marginalization_aux _ _ hm, map_apply _ hms];
  exact measurable_space.measurable_pi_subtype _

end

end probability_theory
