import measure_theory.measure.measure_space
import probability_theory.independence
import probability_theory.conditional

-- TODO subtype.restrict?
def pi_subtype {α : Type*} {β : α → Type*} (mv : set α) := λ (g : Π i, β i) (i : mv), g i

-- TODO change definition of `indep_sets` so this isn't needed
lemma ball_mem_comm' {α β} [has_mem α β] {s t : β} {p : α → α → Prop} :
  (∀ a ∈ s, ∀ b ∈ t, p a b) ↔ (∀ a b, a ∈ s → b ∈ t → p a b) := by tauto

namespace measurable_space

lemma measurable_pi_subtype {δ : Type*} {π : δ → Type*}
  [hmp : Π a, measurable_space (π a)] (s : set δ) :
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

lemma map_map' {α β γ : Type*} [measurable_space α] [measurable_space β] [measurable_space γ]
{g : β → γ} {f : α → β} [hg : fmeas g] [hf : fmeas f] (μ : measure α) :
  map g (map f μ) = map (g ∘ f) μ := map_map hg.fmeas hf.fmeas

lemma map_apply' {α : Type*} {β : Type*} [measurable_space α] [measurable_space β]
  {μ : measure α} {f : α → β} [hfm : fmeas f] (s : set β) [hms : meas s]
  : map f μ s = μ (f ⁻¹' s) := map_apply hfm.fmeas hms.meas

def indep_sets_iff {α} [measurable_space α] (s1 s2 : set (set α))
  (μ : measure α . volume_tac) [is_probability_measure μ]
  (hs1 : s1 ⊆ measurable_set) (hs2 : s2 ⊆ measurable_set) :
  indep_sets s1 s2 μ ↔ (∀ t1 t2 : set α, t1 ∈ s1 → t2 ∈ s2 → indep_set t1 t2 μ) :=
begin
  rw indep_sets,
  repeat {rw forall_congr, intro},
  refine (indep_set_iff_measure_inter_eq_mul (hs1 _) (hs2 _) μ).symm;
  assumption
end

instance fmeas_pi_of {α : Type*} {δ : Type*} {π : δ → Type*}
  [measurable_space α] [Π (a : δ), measurable_space (π a)]
  {g : α → Π (a : δ), π a} [hmg : fmeas g] (a : δ) :
  fmeas (λ (x : α), g x a) := ⟨measurable_pi_iff.mp hmg.fmeas a⟩

instance fmeas_pi_from {α : Type*} {δ : Type*} {π : δ → Type*}
  [measurable_space α] [Π (a : δ), measurable_space (π a)]
  {g : α → Π (a : δ), π a} [hmg : ∀ (a : δ), fmeas (λ (x : α), g x a)] :
  fmeas g  := ⟨measurable_pi_iff.mpr (λ a, (hmg a).fmeas)⟩

instance fmeas_pi_subtype {δ : Type*} {π : δ → Type*}
  [hmp : Π a, measurable_space (π a)] (s : set δ) :
  fmeas (@pi_subtype δ π s) := ⟨measurable_pi_subtype s⟩

instance meas_preimage_of_fmeas_meas
  {α : Type*} {β : Type*} [measurable_space α] [measurable_space β]
  {f : α → β} [hfm : fmeas f] (s : set β) [hms : meas s] :
  meas (f ⁻¹' s) := ⟨fmeas.fmeas hms.meas⟩

------------

variables {α : Type*} [m : measurable_space α] (μ : measure α) {ι: Type*}
  {β : ι → Type*} [hmsb : (Π i : ι, measurable_space (β i))] (f : Π i : ι, α → (β i))

include hmsb

section definitions

/-- The joint distribution induced by an indexed family of random variables `f`. -/
def joint : measure (Π i : ι, β i) := map (λ a i, f i a) μ

instance [is_probability_measure μ] : is_probability_measure (joint μ f) := sorry

/-- The marginal distribution induced by an indexed family of random variables `f`
restriced to a subset of "marginalizing variable" indices `mv` (represented as
an index subtype). -/
def marginal (mv : set ι) : measure (Π i : mv, β i) := joint μ (pi_subtype mv f)

instance [is_probability_measure μ] (mv : set ι) : is_probability_measure (marginal μ f mv) := sorry

/-- Generic marginalization of the joint measure `μ` on the given subset of variables `mv`. -/
def marginalization (μ : measure (Π i : ι, β i)) (mv : set ι) :
  measure (Π i : mv, β i) := map (pi_subtype mv) μ

end definitions

section marginal

variable [hm : ∀ i : ι, fmeas (f i)]
include hm

lemma marginal_eq_marginalization_aux (mv : set ι) :
  marginal μ f mv = marginalization (joint μ f) mv :=
by rw [marginalization, joint, map_map', function.comp]; refl

/-- The marginalization principle: the marginal probability of a particular 
"marginal assignment" measurable set `s` is equal to the joint probability of
that same set, extended to allow the unassigned variables to take any value. -/
theorem marginal_def (mv : set ι) 
  (s : set (Π i : mv, β i)) [hms : meas s] :
  marginal μ f mv s = joint μ f ((pi_subtype mv) ⁻¹' s) :=
by rw [marginal_eq_marginalization_aux, marginalization, map_apply' s]; apply_instance

end marginal

-----

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

-----

section conditional

section definitions

def cond (A B : set ι) (c : set (Π i : B, β i)) : measure (Π i : A, β i) := 
  marginal (cond_measure μ ((λ a i, f i a) ⁻¹' ((pi_subtype B) ⁻¹' c))) f A

end definitions

theorem cond_def [is_probability_measure μ] [hm : ∀ i : ι, fmeas (f i)] (A B : set ι)
  (c : set (Π i : B, β i)) [hmc : meas c]
  (s : set (Π i : A, β i)) [hms : meas s] :
  cond μ f A B c s = cond_measure (joint μ f) (pi_subtype B ⁻¹' c) (pi_subtype A ⁻¹' s) :=
begin
  rw [cond, marginal_def],
  have : joint (cond_measure μ ((λ a i, f i a) ⁻¹' (pi_subtype B ⁻¹' c))) f
    = cond_measure (joint μ f) (pi_subtype B ⁻¹' c),
  { apply measure.ext,
    intros s' hms',
    haveI := meas.mk hms',
    rw [joint, map_apply' s'],
    simp_rw [cond_measure_def, joint],
    rw [map_apply', map_apply', set.preimage_inter],
    apply_instance },
  rw this
end

lemma comap_subtype_ext {P : set (Π i : ι, β i) → Prop} (A : set ι) :
  (∀ x, (comap_subtype A).measurable_set' x → P x)
  ↔ (∀ x, measurable_set x → P (pi_subtype A ⁻¹' x)) := set.maps_image_to _ _ _ _

lemma comap_subtype_subset (A : set ι) :
  {x | (@comap_subtype _ β _ A).measurable_set' x} ⊆ measurable_set := sorry

theorem independent_iff_cond_irrel [hm : ∀ i : ι, fmeas (f i)] [is_probability_measure μ]
  (A B : set ι) :
  independent μ f A B ↔ ∀ (c : set (Π i : B, β i)), cond_meas (marginal μ f B) c
  → cond μ f A B c = marginal μ f A :=
begin
  rw [independent, indep, indep_sets_iff],
  { simp only [ball_mem_comm'.symm],
    -- FIXME this is just to pattern-match, can I avoid this somehow?
    change (∀ (a : set (Π (i : ι), β i)), (comap_subtype A).measurable_set' a
      → ∀ (b : set (Π (i : ι), β i)), (comap_subtype B).measurable_set' b
      → indep_set a b (joint μ f))
      ↔ ∀ (c : set (Π (i : ↥B), β ↑i)), cond_meas (marginal μ f B) c 
      → cond μ f A B c = marginal μ f A,
    simp_rw comap_subtype_ext,
    conv in (cond _ _ _ _ _ = marginal _ _ _) { rw (propext measure.ext_iff) },
    split;
    intro h,
    { intros c hcmc s hms,
      haveI := meas.mk hms,
      rw [cond_def, marginal_def], 
      refine (indep_set_iff_cond_irrel _ _ _).mp _ _,
      exact indep_sets.symm (h _ hms _ hcmc.meas),
      sorry },
    { intros s hms c hmc,
      haveI := meas.mk hms,
      haveI := meas.mk hmc,
      rw (indep_set_iff_cond_irrel' _ _ _),
      intro hcms,
      have := h c (sorry) s hms,
      rw [cond_def, marginal_def] at this,
      assumption,
      apply_instance,
      apply_instance,
      apply_instance } },
  exact comap_subtype_subset _,
  exact comap_subtype_subset _
end

end conditional

end probability_theory
