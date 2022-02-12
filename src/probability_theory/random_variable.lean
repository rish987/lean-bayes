import measure_theory.measure.measure_space
import measure_theory.constructions.pi
import probability_theory.independence
import probability_theory.conditional
import probability_theory.pi_subtype

def heq_congr {A B C : Type*} (hAB : A = B) {f : A → C} {g : B → C} (hfg : f == g)
  {a : A} {b : B} (hab : a == b) : f a = g b := begin
  revert a b f g, rw hAB,
  intros,
  exact congr (eq_of_heq hfg) (eq_of_heq hab)
end

lemma supr_emptyset' {α β} [complete_lattice α] {f : subtype ∅ → α} :
  (⨆ x : (∅ : set β), f x) = ⊥ := by simp

lemma union_subset_iff_right {α} (p q r : set α) (h : p ⊆ r) : p ∪ q ⊆ r ↔ q ⊆ r :=
by rw set.union_subset_iff; exact and_iff_right h

lemma union_subset_iff_left {α} (p q r : set α) (h : q ⊆ r) : p ∪ q ⊆ r ↔ p ⊆ r :=
by rw set.union_subset_iff; exact and_iff_left h

example {α β : Type*} (f : α → β) (hf : function.surjective f) (b b' : set β) (hi : f ⁻¹' b = f ⁻¹' b') : b = b' := by library_search

lemma pi_Inter_distrib {ι ι': Type*} {α : ι → Type*} {s : set ι} {t : ι' → Π i, set (α i)} :
  s.pi (λ i, ⋂ i', t i' i) = ⋂ i', s.pi (t i') :=
begin
  ext x,
  simp only [set.mem_pi, set.mem_Inter],
  have : (∀ i ∈ s, ∀ i', x i ∈ t i' i) ↔ (∀ i', ∀ i ∈ s, x i ∈ t i' i)
    := ⟨(λ h i' i hi, h i hi i'), (λ h i hi i', h i' i hi)⟩,
  rw this
end

noncomputable theory

namespace measure_theory

def bot_measurable_space {α} : measurable_space α :=
begin
  refine measurable_space.mk (set.union {∅} {set.univ}) _ _ _,
  exact or.inl rfl,
  intros s hs,
  cases hs; change _ = _ at hs; subst hs,
  rw set.compl_empty, exact or.inr rfl,
  rw set.compl_univ, exact or.inl rfl,
  intros f hf,
  -- TODO pull things out into their own lemmas
  by_cases ∃ i : ℕ, f i = set.univ,
    rcases h with ⟨i, hfi⟩,
    have : set.univ ≤ (⋃ (i : ℕ), f i) := by rw ← hfi; exact le_supr f i,
    exact or.inr (top_le_iff.mp this),
  simp at h,
  rw set.Union_eq_empty.mpr (λ x, (hf x).elim id (λ hf, absurd hf (h x))),
  exact or.inl rfl
end

lemma bot_measurable_space_eq_bot {α} : @bot_measurable_space α = ⊥ :=
begin
  refine le_bot_iff.mp _,
  intros i hi,
  cases hi; change _ = _ at hi; subst hi,
  exact @measurable_set.empty _ ⊥,
  exact measurable_set.univ
end

lemma inter_of_generate_from_pi {ι : Type*} {α : ι → Type*} (C : Π i, set (set (α i))) (t : set (Π i, α i)) :
  t ∈ set.pi set.univ '' set.pi set.univ (λ (i : ι), {s : set (α i) | C i s}) →
  ∃ (f : Π i, set (α i)), (∀ i, C i (f i)) ∧ t = ⋂ i, function.eval i ⁻¹' (f i) :=
begin
  classical,
  rintro ⟨t', ht1', ht2'⟩,
  refine ⟨t', λ i, ht1' i (set.mem_univ i), _⟩,
  subst ht2',
  let ft' := λ i, (function.update (λ j : ι, (set.univ : set (α j))) i (t' i)),
  have : t' = λ i, ⋂ i', ft' i' i,
  { ext1 i,
    have : (⋂ (i' : ι), ft' i' i ) = ft' i i,
    refine infi_eq_of_forall_ge_of_forall_gt_exists_lt _ (λ _ h, ⟨i, h⟩),
    { intro i',
      by_cases i = i',
      subst h, exact le_refl _,
      have : ft' i' i = set.univ, { exact dif_neg h },
      rw this, finish },
    rw this, exact eq.symm (dif_pos rfl) },
  rw [this, pi_Inter_distrib],
  congr, ext1 i',
  simp_rw (congr_fun this i').symm,
  exact set.univ_pi_update_univ _ _
end

end measure_theory

open measure_theory measure_theory.measure measurable_space

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
  {β : ι → Type*} (f : Π i : ι, α → (β i))

section definitions

lemma pi_set_to_subtype_img_meas [mm : Π i : ι, measurable_space (β i)] {A B : set ι} (hAB : B ⊆ A) {b : set (Π i : B, β i)} (hmb : measurable_set b)
  : measurable_set (pi_set_to_subtype A B '' b) :=
begin
  change measurable_space.pi.measurable_set' b at hmb,
  revert b,
  -- TODO is there some way to do without this assumption? It would be annoying to have to propagate...
  haveI : fintype B := sorry,
  haveI := fintype.encodable B,
  by_cases nonempty ↥B,
  { refine induction_on_inter generate_from_pi.symm is_pi_system_pi _ _ _ _,
    simp,
    { intros t ht,
      obtain ⟨f, hf, rfl⟩ := inter_of_generate_from_pi _ t ht,
      rw set.inj_on.image_Inter_eq (set.inj_on_of_injective (pi_set_to_subtype_bijective hAB).injective _),
      refine measurable_set.Inter _,
      intro,
      rw pi_set_to_subtype_img_preimage_idx hAB,
      have x : ((mm b).comap (λ g : Π (i : set_to_subtype A B), β i, g ⟨⟨b, hAB b.property⟩, b.property⟩)).measurable_set' ((λ (g : Π (i : set_to_subtype A B), β i), g ⟨⟨b, hAB b.property⟩, b.property⟩) ⁻¹' f b) := ⟨f b, hf b, rfl⟩,
      have y := le_supr (λ i : set_to_subtype A B, (mm i).comap (λ g : Π (i : set_to_subtype A B), β i, g i)) ⟨⟨b, hAB b.property⟩, b.property⟩,
      -- why????
      change set.subset _ _ at y,
      exact y x,
      assumption },
    intros _ _ hmt', have := measurable_set.compl hmt',
    rwa set.image_compl_eq (pi_set_to_subtype_bijective hAB),
    intros, rw set.image_Union, apply measurable_set.Union, assumption },
  haveI : subsingleton (Π i : B, β i) := ⟨λ f g, by ext x; exact absurd (nonempty.intro x) h⟩,
  refine subsingleton.set_cases _ _; intro hmc,
  rw set.image_empty, exact measurable_set.empty,
  rw set.image_univ_of_surjective (pi_set_to_subtype_surjective _ _), exact measurable_set.univ
end

variables [Π i : ι, measurable_space (β i)]

def comap_subtype (S : set ι) :
  measurable_space (Π i : ι, β i) := measurable_space.comap (pi_subtype S) measurable_space.pi

lemma comap_subtype_ext {P : set (Π i : ι, β i) → Prop} (A : set ι) :
  (∀ x, (comap_subtype A).measurable_set' x → P x)
  ↔ (∀ x, measurable_set x → P (>[A] x)) := set.maps_image_to _ _ _ _

lemma comap_subtype_subset (A : set ι) :
  @comap_subtype _ β _ A ≤ measurable_space.pi :=
begin
  simp_rw [comap_subtype, measurable_space.pi, comap_supr,
    measurable_space.comap_comp, function.comp, pi_subtype],
  exact supr_le_supr2 (λ i, ⟨i, le_rfl⟩)
end

lemma pi_set_to_subtype_img_meas' {A B : set ι} (hAB : B ⊆ A) :
  @measurable_space.pi ↥B _ _ = (@measurable_space.pi (set_to_subtype A B) _ _).comap (@pi_set_to_subtype _ β A B) :=
begin
  simp_rw [measurable_space.pi, comap_supr, comap_comp, function.comp],
  refine le_antisymm (supr_le_supr2 (λ i, ⟨⟨⟨i, hAB i.property⟩, i.property⟩, _⟩)) (supr_le_supr2 (λ i, ⟨⟨i, i.property⟩, _⟩));
  convert le_refl _; ext x; rw pi_set_to_subtype_def',
  congr, exact subtype.eq rfl, congr
end

lemma pi_set_to_subtype_img_meas'' {A B : set ι} (hAB : B ⊆ A) :
  (@measurable_space.pi ↥B _ _).map (@pi_set_to_subtype _ β A B) = (@measurable_space.pi (set_to_subtype A B) _ _) := 
begin
  rw pi_set_to_subtype_img_meas' hAB,
  ext s,
  split,
  { rintro ⟨s', hms', hs'⟩,
    rwa (set.preimage_eq_preimage (pi_set_to_subtype_bijective hAB).surjective).mp hs' at hms' },
  intro h, exact ⟨s, h, rfl⟩
end

/-- The joint distribution induced by an indexed family of random variables `f`. -/
def joint : measure (Π i : ι, β i) := map (λ a i, f i a) μ

instance [is_probability_measure μ] : is_probability_measure (joint μ f) := sorry

/-- The marginal distribution induced by an indexed family of random variables `f`
restricted to a subset of "marginalizing variable" indices `mv` (represented as
an index subtype). -/
def marginal (mv : set ι) : measure (Π i : mv, β i) := joint μ (pi_subtype mv f)

instance [is_probability_measure μ] (mv : set ι) : is_probability_measure (marginal μ f mv) := sorry

/-- Generic marginalization of the joint measure `μ` on the given subset of variables `mv`. -/
def marginalization (μ : measure (Π i : ι, β i)) (mv : set ι) :
  measure (Π i : mv, β i) := map (pi_subtype mv) μ

end definitions

variables [Π i : ι, measurable_space (β i)]

section marginal

variables [Π i : ι, measurable_space (β i)] (hm : ∀ i : ι, measurable (f i))

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
  (A B : set ι) : independent μ f A B ↔ cond_independent μ f A B ∅ :=
begin
  rw cond_independent,
  have : @comap_subtype _ β _ ∅ = ⊥ :=
    by rw comap_subtype; convert @comap_bot _ _ (pi_subtype ∅); exact supr_emptyset',
  rw [this, ← bot_measurable_space_eq_bot],
  refine iff.trans (iff.symm _) (union_subset_iff_right _ _ _ _).symm,
  apply cond_indep_univ_iff_indep_set,
  intros a ha, change _ = _ at ha, subst ha,
  exact indep_sets_of_cond_null_measure _ _ _ _ measurable_set.empty (outer_measure.empty _),
end

lemma cond_empty_eq_marginal [is_probability_measure μ]
  (A : set ι) : cond μ f A ∅ set.univ = marginal μ f A := 
by simp_rw [cond, pi_unsubtype_img, set.preimage_univ, cond_univ]

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
      refine measurable_pi_subtype _ _; refine pi_set_to_subtype_img_meas _ (by assumption),
      exact set.subset_union_left _ _, exact set.subset_union_right _ _ },
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
        refine pi_set_to_subtype_img_meas _ (by assumption),
        exact set.subset_union_left _ _, exact set.subset_union_right _ _ },
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
