import measure_theory.measure.measure_space
import probability_theory.independence
import probability_theory.conditional
import probability_theory.pi_subtype

open measure_theory measure_theory.measure measurable_space

def heq_congr {A B C : Type*} (hAB : A = B) {f : A → C} {g : B → C} (hfg : f == g)
  {a : A} {b : B} (hab : a == b) : f a = g b := begin
  revert a b f g, rw hAB,
  intros,
  exact congr (eq_of_heq hfg) (eq_of_heq hab)
end

noncomputable theory

namespace probability_theory

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

@[reducible]
def indep_sets' {α} [measurable_space α] {s1 s2 : set (set α)} (μ : measure α) :=
  ∀ (t1 ∈ s1) (t2 ∈ s2), μ (t1 ∩ t2) = μ (t1) * μ (t2)

lemma indep_sets_eq : @indep_sets = @indep_sets' := by ext; split; exact λ a b c d e, a b d c e

def indep_sets_iff {α} [measurable_space α] (s1 s2 : set (set α))
  (μ : measure α) [is_probability_measure μ]
  (hs1 : s1 ⊆ measurable_set) (hs2 : s2 ⊆ measurable_set) :
  indep_sets s1 s2 μ ↔ (∀ (t1 ∈ s1) (t2 ∈ s2), indep_set t1 t2 μ) :=
begin
  rw [indep_sets_eq],
  repeat {rw forall_congr, intro},
  refine (indep_set_iff_measure_inter_eq_mul (hs1 _) (hs2 _) μ);
  assumption
end

def cond_indep_sets_iff {α} [measurable_space α] (s1 s2 cs : set (set α))
  (μ : measure α) [is_probability_measure μ]
  (hs1 : s1 ⊆ measurable_set) (hs2 : s2 ⊆ measurable_set) (hcs : cs ⊆ measurable_set) :
  cond_indep_sets s1 s2 cs μ ↔ (∀ (t1 ∈ s1) (t2 ∈ s2) (c ∈ cs), cond_indep_set' t1 t2 c μ) := sorry

------------

variables {α : Type*} [m : measurable_space α] (μ : measure α) {ι: Type*}
  {β : ι → Type*} [(Π i : ι, measurable_space (β i))] (f : Π i : ι, α → (β i))

section definitions

-- this one may take quite a bit of work, but assuming B ⊆ A should make it easier...
lemma pi_set_to_subtype_img_meas {A B : set ι} {b : set (Π i : B, β i)} (hmb : measurable_set b)
  : measurable_set (pi_set_to_subtype A B '' b) := sorry

def comap_subtype (S : set ι) :
  measurable_space (Π i : ι, β i) := measurable_space.comap (pi_subtype S) infer_instance

lemma comap_subtype_ext {P : set (Π i : ι, β i) → Prop} (A : set ι) :
  (∀ x, (comap_subtype A).measurable_set' x → P x)
  ↔ (∀ x, measurable_set x → P (>[A] x)) := set.maps_image_to _ _ _ _

lemma comap_subtype_subset (A : set ι) :
  {x | (@comap_subtype _ β _ A).measurable_set' x} ⊆ measurable_set := sorry

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
variable (hm : ∀ i : ι, measurable (f i))
include hm

lemma marginal_eq_marginalization_aux (mv : set ι) :
  marginal μ f mv = marginalization (joint μ f) mv :=
by { rw [marginalization, joint, map_map, function.comp], refl,
  apply measurable_pi_subtype, exact measurable_pi_iff.mpr hm }

/-- The marginalization principle: the marginal probability of a particular 
"marginal assignment" measurable set `s` is equal to the joint probability of
that same set, extended to allow the unassigned variables to take any value. -/
theorem marginal_def (mv : set ι) 
  {s : set (Π i : mv, β i)} (hms : measurable_set s) :
  marginal μ f mv s = joint μ f (>[] s) :=
by { rw [marginal_eq_marginalization_aux _ _ hm, marginalization, map_apply _ hms],
  apply measurable_pi_subtype }

lemma joint_cond_meas_of_marginal (mv : set ι) 
  (s : set (Π i : mv, β i)) (hms : measurable_set s) (hcs : (marginal μ f mv) s ≠ 0) :
  joint μ f (>[] s) ≠ 0 := sorry

lemma marginal_cond_meas_of_joint (mv : set ι) 
  (s : set (Π i : mv, β i)) (hms : measurable_set s) (hcs : (joint μ f) (>[] s) ≠ 0) :
  marginal μ f mv s ≠ 0 := sorry

lemma marginal_cond_meas_of_joint_inter {A B : set ι} {a : set (Π i : A, β i)} {b : set (Π i : B, β i)}
  (hjc : joint μ f (>[] a ∩ >[] b) ≠ 0) : marginal μ f _ (>₁[] a ∩ >₂[] b) ≠ 0 := sorry

lemma joint_cond_meas_of_marginal_inter {A B : set ι} {a : set (Π i : A, β i)} {b : set (Π i : B, β i)}
  (hmc : marginal μ f _ (>₁[] a ∩ >₂[] b) ≠ 0) : joint μ f (>[] a ∩ >[] b) ≠ 0 := sorry

end marginal

-----

section independence

section definitions

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
  marginal (cond_measure μ ((λ a i, f i a) ⁻¹' (>[] c))) f A

/-- Two sets of random variables `A` and `B` are independent given a third set `C`
if the measurable spaces `A` and `B` incur on the joint distribution are independent
given any measurable set incurred by `C`. -/
def cond_independent (A B C : set ι) : Prop :=
  cond_indep (comap_subtype A) (comap_subtype B) (comap_subtype C).measurable_set' (joint μ f)

end definitions

theorem cond_def [is_probability_measure μ] (hm : ∀ i : ι, measurable (f i)) (A B : set ι)
  (c : set (Π i : B, β i)) (hmc : measurable_set c)
  (s : set (Π i : A, β i)) (hms : measurable_set s) :
  cond μ f A B c s = cond_measure (joint μ f) (>[] c) (>[] s) :=
begin
  rw [cond, marginal_def _ _ hm _ hms],
  congr, ext1 s' hms',
  have hm' := measurable_pi_iff.mpr hm,
  have hmc' := measurable_pi_subtype B hmc,
  rw [joint, map_apply, cond_measure_def, cond_measure_def, joint,
    map_apply, map_apply, set.preimage_inter]; try {assumption},
  apply measurable_set.inter hmc' hms',
  exact hm' hmc'
end

lemma independent_iff_cond_independent_empty [is_probability_measure μ]
  (A B : set ι) : independent μ f A B ↔ cond_independent μ f A B ∅ := sorry

lemma cond_empty_eq_marginal [is_probability_measure μ]
  (A : set ι) : cond μ f A ∅ set.univ = marginal μ f A := sorry

theorem cond_independent_iff_cond_inter_irrel [is_probability_measure μ] (hm : ∀ i : ι, measurable (f i))
  (A B C : set ι) :
  cond_independent μ f A B C ↔ ∀ (b : set (Π i : B, β i)) (hmb : measurable_set b)
  (c : set (Π i : C, β i)) (hmc : measurable_set c),
  marginal μ f (B ∪ C) (>₁[] b ∩ >₂[] c) ≠ 0
  → cond μ f A (B ∪ C) (>₁[] b ∩ >₂[] c) = cond μ f A C c :=
begin
  rw [cond_independent, cond_indep, cond_indep_sets_iff],
  { -- FIXME this is just to pattern-match, can I avoid this somehow?
    change (
        ∀ (a : set (Π (i : ι), β i)), (comap_subtype A).measurable_set' a
      → ∀ (b : set (Π (i : ι), β i)), (comap_subtype B).measurable_set' b
      → ∀ (c : set (Π (i : ι), β i)), (comap_subtype C).measurable_set' c
      → cond_indep_set' a b c (joint μ f))
      ↔ ∀ (b : set (Π (i : ↥B), β ↑i)) (hmb : measurable_set b)
      (c : set (Π (i : ↥C), β ↑i)) (hmc : measurable_set c),
      marginal μ f (B ∪ C) (>₁[] b ∩ >₂[] c) ≠ 0
      → cond μ f A (B ∪ C) (>₁[] b ∩ >₂[] c) = cond μ f A C c,
    simp_rw comap_subtype_ext,
    conv in (cond _ _ _ _ _ = cond _ _ _ _ _) { rw measure.ext_iff },
    split; intro h,
    { intros b hmb c hmc hcmbc a hma,
      have : joint μ f (>[] b ∩ >[] c) ≠ 0
        := joint_cond_meas_of_marginal_inter _ _ hm hcmbc,
      rw set.inter_comm at this,
      rw [cond_def, cond_def]; try {assumption},
      convert (cond_indep_set_iff_cond_inter_irrel (joint μ f) _ _ _).mp
        (cond_indep_set'.symm (h _ hma _ hmb _ hmc)) _;
      try {exact measurable_pi_subtype _ (by assumption)},
      rw [pi_unsubtype_union_img_inter₁₂, set.inter_comm],
      assumption,
      refine measurable_set.inter _ _;
      refine measurable_pi_subtype _ _;
      exact pi_set_to_subtype_img_meas (by assumption) },
    { intros a hma b hmb c hmc,
      rw cond_indep_set_iff_cond_inter_irrel',
      intro hcmbc,
      rw set.inter_comm at hcmbc,
      have : marginal μ f _ (>₁[] b ∩ >₂[] c) ≠ 0 
        := marginal_cond_meas_of_joint_inter _ _ hm hcmbc,
      have := h b _ c _ _ a hma; try {assumption},
      rw [cond_def, cond_def] at this; try {assumption},
      rwa [set.inter_comm, ← pi_unsubtype_union_img_inter₁₂],
      { refine measurable_set.inter _ _;
        refine measurable_pi_subtype _ _;
        exact pi_set_to_subtype_img_meas (by assumption) },
      all_goals {exact measurable_pi_subtype _ (by assumption)} } },
  all_goals {exact comap_subtype_subset _}
end

theorem independent_iff_cond_irrel  [is_probability_measure μ] (hm : ∀ i : ι, measurable (f i))
  (A B : set ι) :
  independent μ f A B ↔ ∀ (b : set (Π i : B, β i)) (hmb : measurable_set b), marginal μ f B b ≠ 0
  → cond μ f A B b = marginal μ f A :=
begin
  convert cond_independent_iff_cond_inter_irrel μ f hm A B ∅; ext,
  exact independent_iff_cond_independent_empty _ _ A B,
  refine forall_congr _, intro b,
  refine forall_congr _, intro hmb,
  haveI : subsingleton (Π i : (∅ : set ι), β i) := ⟨λ f g, by ext ⟨x, hx⟩; exact false.elim hx⟩,
  have h1 : ⇑(marginal μ f (B ∪ ∅)) == ⇑(marginal μ f B) := by rw set.union_empty,
  have h2 : cond μ f A (B ∪ ∅) == cond μ f A B := by rw set.union_empty,
  have h3 : >₁[B,∅] b == b := begin
    rw [pi_unsubtype_union_img₁, set.union_empty],
    refine heq_of_eq _,
    exact pi_unsubtype_set_same _ _
  end,
  have : (marginal μ f (B ∪ ∅) (>₁[] b ∩ >₂[] set.univ) ≠ 0
    → cond μ f A (B ∪ ∅) (>₁[] b ∩ >₂[] set.univ) = cond μ f A ∅ set.univ)
    ↔ (marginal μ f B b ≠ 0 → cond μ f A B b = marginal μ f A),
  { simp_rw [pi_unsubtype_union_img₂, pi_unsubtype_set, pi_unsubtype_img,
      set.image_univ_of_surjective (pi_set_to_subtype_surjective _ _), set.preimage_univ, set.inter_univ],
    rw heq_congr (by rw set.union_empty) h1 h3,
    rw heq_congr (by rw set.union_empty) h2 h3,
    rw cond_empty_eq_marginal },
  split; intro h,
  { refine subsingleton.set_cases _ _; intro hmc,
    simp_rw [pi_unsubtype_union_img₂, pi_unsubtype_set, pi_unsubtype_img],
    simp_rw [set.image_empty, set.preimage_empty, set.inter_empty],
    intro h', exact absurd (outer_measure.empty' _) h',
    rwa this },
  { have h' := h set.univ measurable_set.univ,
    rwa this at h' },
end

end conditional

end probability_theory
