import measure_theory.measure.measure_space

noncomputable theory

open measure_theory measure_theory.measure measurable_space

section

variables {α : Type*} [m : measurable_space α] (μ : measure α) {ι: Type*}
  {β : ι → Type*} [hms : (Π i : ι, measurable_space (β i))] (f : Π i : ι, α → (β i))

include hms

def joint : measure (Π i : ι, β i) := map (λ a i, f i a) μ

def marginal (mv : set ι) : measure (Π i : mv, β i) :=
  joint μ (λ (i : mv) a, f i a)

theorem marginalization (hm : ∀ i : ι, measurable (f i)) (mv : set ι) :
  marginal μ f mv = map (λ (g : Π i, β i) (i : mv), g i) (joint μ f) :=
begin
  rw [joint, map_map _ (measurable_pi_iff.mpr hm), function.comp],
  refl,
  rw measurable_pi_iff,
  intro a,
  rw measurable_iff_comap_le,
  -- FIXME why can't the lambda below be inferred?
  exact le_supr (λ a, (hms a).comap (λ (b : Π a, β a), b a)) _,
end

end
