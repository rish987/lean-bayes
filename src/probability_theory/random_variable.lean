import measure_theory.measure.measure_space
import probability_theory.independence
import probability_theory.conditional

-- TODO does this already exist?
def pi_subtype {α : Type*} {β : α → Type*} (mv : set α) := λ (g : Π i, β i) (i : mv), g i

namespace measurable_space

variables {δ : Type*} {π : δ → Type*}
  [hmp : Π a, measurable_space (π a)]
include hmp

lemma measurable_pi_subtype (s : set δ) :
  measurable (@pi_subtype δ π s) :=
begin
  rw measurable_pi_iff,
  intro a,
  rw measurable_iff_comap_le,
  -- FIXME why can't the lambda below be inferred?
  exact le_supr (λ a, (hmp a).comap (λ (b : Π a, π a), b a)) _,
end

end measurable_space

open measure_theory measure_theory.measure measurable_space

noncomputable theory

namespace probability_theory

variables {α : Type*} [m : measurable_space α] (μ : measure α) {ι: Type*}
  {β : ι → Type*} [hmsb : (Π i : ι, measurable_space (β i))] (f : Π i : ι, α → (β i))

include hmsb

section definitions

/-- The joint distribution induced by an indexed family of random variables `f`. -/
def joint : measure (Π i : ι, β i) := map (λ a i, f i a) μ

/-- The marginal distribution induced by an indexed family of random variables `f`
restriced to a subset of "marginalizing variable" indices `mv` (represented as
an index subtype). -/
def marginal (mv : set ι) : measure (Π i : mv, β i) := joint μ (pi_subtype mv f)

/-- Generic marginalization of the joint measure `μ` on the given subset of variables `mv`. -/
def marginalization (μ : measure (Π i : ι, β i)) (mv : set ι) :
  measure (Π i : mv, β i) := map (pi_subtype mv) μ

end definitions

section marginal

variable (hm : ∀ i : ι, measurable (f i))
include hm

lemma marginal_eq_marginalization_aux (mv : set ι) :
  marginal μ f mv = marginalization (joint μ f) mv :=
by rw [marginalization, joint, map_map _ (measurable_pi_iff.mpr hm), function.comp];
  try {refl}; exact measurable_pi_subtype _

/-- The marginal probability of a particular "marginal assignment" measurable set `s`
is equal to the joint probability of that same set, extended to allow the unassigned
variables to take any value. -/
theorem marginal_eq_marginalization (mv : set ι) 
  (s : set (Π i : mv, β i)) (hms : measurable_set s) :
  marginal μ f mv s = joint μ f ((pi_subtype mv) ⁻¹' s) :=
by rw [marginal_eq_marginalization_aux _ _ hm, marginalization, map_apply _ hms];
  exact measurable_pi_subtype _

end marginal

section conditional

def cond (A B : set ι) (c : set (Π i : B, β i)) : measure (Π i : A, β i) := 
  marginal (cond_measure μ ((λ a i, f i a) ⁻¹' ((pi_subtype B) ⁻¹' c))) f A

end conditional

section independence

section definitions

def comap_subtype (S : set ι) :
  measurable_space (Π i : ι, β i) := measurable_space.comap (pi_subtype S) infer_instance

/-- A list of sets of random variables `S` is independent if the list of measurable spaces
it incurs on the joint distribution is independent. -/
def Independent {ι' : Type*} (S : ι' → set ι) : Prop :=
  Indep (λ i, comap_subtype (S i)) (joint μ f)

/-- Two sets of random variables `A` and `B` are independent if the measurable spaces
they incur on the joint distribution are independent. -/
def independent (A B : set ι) : Prop :=
  indep (comap_subtype A) (comap_subtype B) (joint μ f)

end definitions

end independence

end probability_theory
