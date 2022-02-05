import measure_theory.measure.measure_space
import probability_theory.independence
import probability_theory.conditional

namespace set

theorem image_inter_on' {α β} {f : α → β} {s t : set α}
  (h : ∀ (x ∈ s \ t) (y ∈ t \ s), f x ≠ f y) :
  f '' s ∩ f '' t = f '' (s ∩ t) :=
begin
  refine subset.antisymm _ (image_inter_subset _ _ _),
  rintro _ ⟨⟨a, has, hab⟩, ⟨b, hbt, rfl⟩⟩,
  by_cases hat : a ∈ t, { exact hab ▸ mem_image_of_mem f ⟨has, hat⟩ },
  by_cases hbs : b ∈ s, { exact mem_image_of_mem f ⟨hbs, hbt⟩ },
  exact absurd hab (h a ⟨has, hat⟩ b ⟨hbt, hbs⟩)
end

end set

-- TODO subtype.restrict?
def pi_subtype {α : Type*} {β : α → Type*} (mv : set α) := λ (g : Π i, β i) (i : mv), g i

@[reducible]
def pi_subtype_img {α : Type*} {β : α → Type*} (mv : set α) :=
  λ (g : set (Π i, β i)) , pi_subtype mv '' g

@[reducible]
def pi_unsubtype_img {α : Type*} {β : α → Type*} (mv : set α) :=
  λ (g : set (Π i : mv, β i)), pi_subtype mv ⁻¹' g

notation  `<[`S`]` := pi_subtype_img S
notation  `>[`S`]` := pi_unsubtype_img S

notation  `<[]` := pi_subtype_img _
notation  `>[]` := pi_unsubtype_img _

@[reducible]
def pi_unsubtype_union_img₁ {α : Type*} {β : α → Type*} (A : set α) (B : set α) :
  set (Π i : A, β i) → set (Π i : A ∪ B, β i) := λ g, <[A ∪ B] (>[A] g)

@[reducible]
def pi_unsubtype_union_img₂ {α : Type*} {β : α → Type*} (A : set α) (B : set α) :
  set (Π i : B, β i) → set (Π i : A ∪ B, β i) := λ g, <[A ∪ B] (>[B] g)

def set_to_subtype {α : Type*} (A : set α) (B : set α) : set A := λ x : A, ↑x ∈ B

def pi_set_to_subtype {α : Type*} {β : α → Type*} (A : set α) (B : set α)
  (f : Π i : B, β i) : Π i : set_to_subtype A B, β i := λ ⟨i, hi⟩, f ⟨i, hi⟩

lemma pi_subtype_ext' {α : Type*} {β : α → Type*} {A : set α} {f : Π i, β i} {g : Π i : A, β i} : pi_subtype A f = g ↔ ∀ i : A, f i = g i := sorry
lemma pi_subtype_ext {α : Type*} {β : α → Type*} {A : set α} {f g : Π i, β i} : pi_subtype A f = pi_subtype A g ↔ ∀ i ∈ A, f i = g i := sorry

notation  `>₁[`A`,`B`]` := pi_unsubtype_union_img₁ A B
notation  `>₂[`A`,`B`]` := pi_unsubtype_union_img₂ A B

notation  `>₁[]` := pi_unsubtype_union_img₁ _ _
notation  `>₂[]` := pi_unsubtype_union_img₂ _ _

lemma pi_subtype_subtype {α : Type*} {β : α → Type*} (A : set α) (B : set α)
  (x : Π i : α, β i) : pi_subtype (set_to_subtype A B) (pi_subtype A x) = λ (i : set_to_subtype A B), x i := rfl

example {α : Type*} {β : α → Type*} (A : set α) (B : set α) (sb : set (Π i : B, β i))
  : >₂[] sb = @pi_unsubtype_img _ (pi_subtype (A ∪ B) β) _ (pi_set_to_subtype (A ∪ B) B '' sb) := sorry

example {α : Type*} {β : α → Type*} (A : set α) (B : set α) (sb : set (Π i : B, β i)) (hba : B ⊆ A)
  : >[B] sb = >[A] (@pi_unsubtype_img _ (pi_subtype A β) _ (pi_set_to_subtype A B '' sb)) :=
begin
  simp_rw pi_unsubtype_img,
  rw set.preimage_preimage,
  conv in (pi_subtype (set_to_subtype A B) (pi_subtype A _)) {rw pi_subtype_subtype},
  have : ∀ (x : Π (i : α), β i), pi_subtype B x ∈ sb ↔ (λ (i : ↥(set_to_subtype A B)), x ↑i) ∈ (pi_set_to_subtype A B '' sb),
  { intro x, split; intro h,
    { refine ⟨pi_subtype B x, h, _⟩,
      ext ⟨⟨_, _⟩, _⟩,
      dsimp [pi_set_to_subtype, pi_subtype],
      refl },
    { obtain ⟨x', hxsb, hx'⟩ := h,
      convert hxsb,
      refine pi_subtype_ext'.mpr _,
      rintro ⟨i, hi⟩,
      exact (congr_fun hx' ⟨⟨i, hba hi⟩, hi⟩).symm } } ,
  refine set.subset.antisymm _ _;
  intro x, exact (this x).mp, exact (this x).mpr
end

example {α : Type*} {β : α → Type*} (A : set α) (B : set α)
  (a : set (Π i : A, β i)) (b : set (Π i : B, β i)) : >[] (>₁[] a ∩ >₂[] b) = >[] a ∩ >[] b :=
begin
  simp_rw pi_unsubtype_img,
  rw set.preimage_inter,
  simp_rw pi_unsubtype_union_img₁,
  simp_rw pi_unsubtype_union_img₂,
  simp_rw pi_subtype_img,
  simp_rw set.preimage_image_eq _ (sorry)
end

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

@[reducible]
def indep_sets' {α} [measurable_space α] {s1 s2 : set (set α)} (μ : measure α) :=
  ∀ (t1 ∈ s1) (t2 ∈ s2), μ (t1 ∩ t2) = μ (t1) * μ (t2)

lemma indep_sets_eq : @indep_sets = @indep_sets' := by ext; split; exact λ a b c d e, a b d c e

def indep_sets_iff {α} [measurable_space α] (s1 s2 : set (set α))
  (μ : measure α . volume_tac) [is_probability_measure μ]
  (hs1 : s1 ⊆ measurable_set) (hs2 : s2 ⊆ measurable_set) :
  indep_sets s1 s2 μ ↔ (∀ (t1 ∈ s1) (t2 ∈ s2), indep_set t1 t2 μ) :=
begin
  rw [indep_sets_eq],
  repeat {rw forall_congr, intro},
  refine (indep_set_iff_measure_inter_eq_mul (hs1 _) (hs2 _) μ);
  assumption
end

def cond_indep_sets_iff {α} [measurable_space α] (s1 s2 cs : set (set α))
  (μ : measure α . volume_tac) [is_probability_measure μ]
  (hs1 : s1 ⊆ measurable_set) (hs2 : s2 ⊆ measurable_set) (hcs : cs ⊆ measurable_set) :
  cond_indep_sets s1 s2 cs μ ↔ (∀ (t1 ∈ s1) (t2 ∈ s2) (c ∈ cs), cond_indep_set' t1 t2 c μ) := sorry

instance fmeas_pi_of {α : Type*} {δ : Type*} {π : δ → Type*}
  [measurable_space α] [Π (a : δ), measurable_space (π a)]
  {g : α → Π (a : δ), π a} [hmg : fmeas g] (a : δ) :
  fmeas (λ (x : α), g x a) := ⟨measurable_pi_iff.mp hmg.fmeas a⟩

instance fmeas_pi_from {α : Type*} {δ : Type*} {π : δ → Type*}
  [measurable_space α] [Π (a : δ), measurable_space (π a)]
  {g : α → Π (a : δ), π a} [hmg : ∀ (a : δ), fmeas (λ (x : α), g x a)] :
  fmeas g  := ⟨measurable_pi_iff.mpr (λ a, (hmg a).fmeas)⟩

instance fmeas_pi_subtype {δ : Type*} {π : δ → Type*}
  [Π a, measurable_space (π a)] (s : set δ) :
  fmeas (@pi_subtype δ π s) := ⟨measurable_pi_subtype s⟩

instance meas_preimage_of_fmeas_meas
  {α : Type*} {β : Type*} [measurable_space α] [measurable_space β]
  {f : α → β} [hfm : fmeas f] (s : set β) [hms : meas s] :
  meas (f ⁻¹' s) := ⟨fmeas.fmeas hms.meas⟩

------------

variables {α : Type*} [m : measurable_space α] (μ : measure α) {ι: Type*}
  {β : ι → Type*} [(Π i : ι, measurable_space (β i))] (f : Π i : ι, α → (β i))

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
  (s : set (Π i : mv, β i)) [meas s] :
  marginal μ f mv s = joint μ f (>[] s) :=
by rw [marginal_eq_marginalization_aux, marginalization, map_apply' s];
  apply_instance

instance joint_cond_meas_of_marginal (mv : set ι) 
  (s : set (Π i : mv, β i)) [hms : meas s] [cond_meas (marginal μ f mv) s]
  : cond_meas (joint μ f) (>[] s) := sorry

instance marginal_cond_meas_of_joint (mv : set ι) 
  (s : set (Π i : mv, β i)) [hms : meas s] [cond_meas (joint μ f) (>[] s)]
  : cond_meas (marginal μ f mv) s := sorry

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
  marginal (cond_measure μ ((λ a i, f i a) ⁻¹' (>[] c))) f A

/-- Two sets of random variables `A` and `B` are independent given a third set `C`
if the measurable spaces `A` and `B` incur on the joint distribution are independent
given any measurable set incurred by `C`. -/
def cond_independent (A B C : set ι) : Prop :=
  cond_indep (comap_subtype A) (comap_subtype B) (comap_subtype C).measurable_set' (joint μ f)

end definitions

theorem cond_def [is_probability_measure μ] [∀ i : ι, fmeas (f i)] (A B : set ι)
  (c : set (Π i : B, β i)) [meas c]
  (s : set (Π i : A, β i)) [meas s] :
  cond μ f A B c s = cond_measure (joint μ f) (>[] c) (>[] s) :=
begin
  rw [cond, marginal_def],
  have : joint (cond_measure μ ((λ a i, f i a) ⁻¹' (>[] c))) f
    = cond_measure (joint μ f) (>[] c),
  { apply measure.ext,
    intros s' hms',
    haveI := meas.mk hms',
    rw [joint, map_apply'],
    simp_rw [cond_measure_def, joint],
    rw [map_apply', map_apply', set.preimage_inter] },
  rw this
end

lemma comap_subtype_ext {P : set (Π i : ι, β i) → Prop} (A : set ι) :
  (∀ x, (comap_subtype A).measurable_set' x → P x)
  ↔ (∀ x, measurable_set x → P (>[A] x)) := set.maps_image_to _ _ _ _

lemma comap_subtype_subset (A : set ι) :
  {x | (@comap_subtype _ β _ A).measurable_set' x} ⊆ measurable_set := sorry

theorem cond_independent_iff_cond_inter_irrel [∀ i : ι, fmeas (f i)] [is_probability_measure μ]
  (A B C : set ι) :
  cond_independent μ f A B C ↔ ∀ (b : set (Π i : B, β i)) (c : set (Π i : C, β i)),
  meas b → meas c → cond_meas (marginal μ f (B ∪ C)) (>₁[] b ∩ >₂[] c)
  → cond μ f A (B ∪ C) (>₁[] b ∩ >₂[] c) = cond μ f A C c :=
begin
  rw [cond_independent, cond_indep, cond_indep_sets_iff],
  { -- FIXME this is just to pattern-match, can I avoid this somehow?
    change (
        ∀ (a : set (Π (i : ι), β i)), (comap_subtype A).measurable_set' a
      → ∀ (b : set (Π (i : ι), β i)), (comap_subtype B).measurable_set' b
      → ∀ (c : set (Π (i : ι), β i)), (comap_subtype C).measurable_set' c
      → cond_indep_set' a b c (joint μ f))
      ↔ ∀ (b : set (Π (i : ↥B), β ↑i)) (c : set (Π (i : ↥C), β ↑i)), 
      meas b → meas c →
      cond_meas (marginal μ f (B ∪ C)) (>₁[] b ∩ >₂[] c)
      → cond μ f A (B ∪ C) (>₁[] b ∩ >₂[] c) = cond μ f A C c,
    simp_rw comap_subtype_ext,
    conv in (cond _ _ _ _ _ = cond _ _ _ _ _) { rw measure.ext_iff },
    split;
    intro h,
    { intros b c hmb hmc hcmbc a hma,
      -- TODO can I make this more concise?
      haveI := hcmbc,
      haveI := hmb,
      haveI := hmc,
      haveI := meas.mk hma,
      -- FIXME why was this necessary?
      haveI := meas.mk hcmbc.meas,
      simp_rw [cond_def],
      convert (cond_indep_set_iff_cond_inter_irrel (joint μ f) (>[] b) (>[] a) (>[] c)).mp
        (cond_indep_set'.symm (h _ hma _ hmb.meas _ hmc.meas)) _,
      rw set.image_inter_on' _,
      simp_rw pi_unsubtype_img,
      simp_rw set.preimage_image_eq (>[] b ∩ >[] c) (sorry),
      rw set.inter_comm,
      { rintro _ ⟨_, hx'⟩ _ ⟨hy, _⟩ heq,
        have := pi_subtype_ext.mpr (λ i hi, pi_subtype_ext.mp heq i (or.inr hi)),
        exact hx' (this.symm ▸ hy : pi_subtype C x ∈ c) },
      sorry
    },
    { intros a hma b hmb c hmc,
      haveI := meas.mk hma,
      haveI := meas.mk hmb,
      haveI := meas.mk hmc,
      rw cond_indep_set_iff_cond_inter_irrel',
      intro hcmbc,
      haveI := hcmbc,
      haveI : meas (>₁[] b ∩ >₂[] c) := sorry,
      have := h b c (meas.mk hmb) (meas.mk hmc) (sorry) a hma,
      rw [cond_def, cond_def] at this,
      have temp : (>[] (>₁[] b ∩ >₂[] c)) = (>[] c ∩ >[] b) := sorry,
      rwa temp at this,
    } },
  exact comap_subtype_subset _,
  exact comap_subtype_subset _,
  exact comap_subtype_subset _
end

-- TODO prove this concisely using the above theorem when C = ∅
theorem independent_iff_cond_irrel [∀ i : ι, fmeas (f i)] [is_probability_measure μ]
  (A B : set ι) :
  independent μ f A B ↔ ∀ (c : set (Π i : B, β i)), cond_meas (marginal μ f B) c
  → cond μ f A B c = marginal μ f A :=
begin
  rw [independent, indep, indep_sets_iff],
  { -- FIXME this is just to pattern-match, can I avoid this somehow?
    change (∀ (a : set (Π (i : ι), β i)), (comap_subtype A).measurable_set' a
      → ∀ (b : set (Π (i : ι), β i)), (comap_subtype B).measurable_set' b
      → indep_set a b (joint μ f))
      ↔ ∀ (c : set (Π (i : ↥B), β ↑i)), cond_meas (marginal μ f B) c 
      → cond μ f A B c = marginal μ f A,
    simp_rw comap_subtype_ext,
    conv in (cond _ _ _ _ _ = marginal _ _ _) { rw measure.ext_iff },
    split;
    intro h,
    { intros c hcmc s hms,
      haveI := meas.mk hms,
      rw [cond_def, marginal_def], 
      exact (indep_set_iff_cond_irrel _ _ _).mp
        (indep_sets.symm (h _ hms _ hcmc.meas)) infer_instance },
    { intros s hms c hmc,
      haveI := meas.mk hms,
      haveI := meas.mk hmc,
      rw indep_set_iff_cond_irrel',
      intro hcms,
      haveI := hcms,
      have := h c infer_instance s hms,
      rwa [cond_def, marginal_def] at this } },
  exact comap_subtype_subset _,
  exact comap_subtype_subset _
end

end conditional

end probability_theory
