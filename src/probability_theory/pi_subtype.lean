import data.set

namespace probability_theory

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

def set_to_subtype {α : Type*} (A : set α) (B : set α) : set A := λ x : A, ↑x ∈ B

def pi_set_to_subtype {α : Type*} {β : α → Type*} (A : set α) (B : set α)
  (f : Π i : B, β i) : Π i : set_to_subtype A B, β i := λ ⟨i, hi⟩, f ⟨i, hi⟩

-- TODO generalize to set-indexed version using `Union`
@[reducible]
def pi_unsubtype_union_img₁ {α : Type*} {β : α → Type*} (A : set α) (B : set α) :
  set (Π i : A, β i) → set (Π i : A ∪ B, β i)
  := λ g, >[set_to_subtype (A ∪ B) A] (pi_set_to_subtype (A ∪ B) A '' g)

@[reducible]
def pi_unsubtype_union_img₂ {α : Type*} {β : α → Type*} (A : set α) (B : set α) :
  set (Π i : B, β i) → set (Π i : A ∪ B, β i)
  := λ g, >[set_to_subtype (A ∪ B) B] (pi_set_to_subtype (A ∪ B) B '' g)

lemma pi_subtype_ext' {α : Type*} {β : α → Type*} {A : set α}
{f : Π i, β i} {g : Π i : A, β i} : pi_subtype A f = g ↔ ∀ i : A, f i = g i := sorry

lemma pi_subtype_ext {α : Type*} {β : α → Type*} {A : set α} {f g : Π i, β i} :
pi_subtype A f = pi_subtype A g ↔ ∀ i ∈ A, f i = g i := sorry

notation `>₁[`A`,`B`]` := pi_unsubtype_union_img₁ A B
notation `>₂[`A`,`B`]` := pi_unsubtype_union_img₂ A B

notation `>₁[]` := pi_unsubtype_union_img₁ _ _
notation `>₂[]` := pi_unsubtype_union_img₂ _ _

lemma pi_subtype_subtype {α : Type*} {β : α → Type*} (A : set α) (B : set α) 
  (x : Π i : α, β i) :
  pi_subtype (set_to_subtype A B) (pi_subtype A x) = λ (i : set_to_subtype A B), x i := rfl

def pi_unsubtype_union_img_def₁ {α : Type*} {β : α → Type*} [∀ i : α, inhabited (β i)]
  (A : set α) (B : set α) (sb : set (Π i : A, β i)) : >₁[A,B] sb = <[A ∪ B] (>[A] sb) :=
begin
  simp_rw [pi_unsubtype_union_img₁, pi_unsubtype_img, pi_subtype_img],
  refine set.subset.antisymm _ _; intros x h,
  { obtain ⟨x', h', h⟩ := h,
    classical,
    let y : Π i, β i := λ i, if h : i ∈ A then x' ⟨i, h⟩
      else if h : i ∈ A ∪ B then x ⟨i, h⟩ else default,
    refine ⟨y, _, _⟩,
    change pi_subtype A y ∈ sb,
    convert h',
    all_goals {refine pi_subtype_ext'.mpr _, rintro ⟨i, hi⟩},
      exact dif_pos hi,
    by_cases hi' : i ∈ A,
      convert dif_pos hi',
      exact (congr_fun h ⟨⟨_, hi⟩, hi'⟩).symm,
    exact (dif_neg hi').trans (dif_pos hi) },
  { obtain ⟨_, h', rfl⟩ := h,
    refine ⟨pi_subtype A _, h', _⟩,
    ext ⟨⟨_, _⟩, _⟩, refl }
end

-- TODO shouldn't need this duplicate once have generalized to `Union`
def pi_unsubtype_union_img_def₂ {α : Type*} {β : α → Type*} [∀ i : α, inhabited (β i)]
  (A : set α) (B : set α) (sb : set (Π i : B, β i)) : >₂[A,B] sb = <[A ∪ B] (>[B] sb) :=
begin
  simp_rw [pi_unsubtype_union_img₂, pi_unsubtype_img, pi_subtype_img],
  refine set.subset.antisymm _ _; intros x h,
  { obtain ⟨x', h', h⟩ := h,
    classical,
    let y : Π i, β i := λ i, if h : i ∈ B then x' ⟨i, h⟩
      else if h : i ∈ A ∪ B then x ⟨i, h⟩ else default,
    refine ⟨y, _, _⟩,
    change pi_subtype B y ∈ sb,
    convert h',
    all_goals {refine pi_subtype_ext'.mpr _, rintro ⟨i, hi⟩},
      exact dif_pos hi,
    by_cases hi' : i ∈ B,
      convert dif_pos hi',
      exact (congr_fun h ⟨⟨_, hi⟩, hi'⟩).symm,
    exact (dif_neg hi').trans (dif_pos hi) },
  { obtain ⟨_, h', rfl⟩ := h,
    refine ⟨pi_subtype B _, h', _⟩,
    ext ⟨⟨_, _⟩, _⟩, refl }
end

def pi_subtype_subtype_subset {α : Type*} {β : α → Type*} {A : set α} {B : set α}
  (hba : B ⊆ A) (sb : set (Π i : B, β i)) :
  >[B] sb = >[A] (>[set_to_subtype A B] (pi_set_to_subtype A B '' sb)) :=
begin
  simp_rw [pi_unsubtype_img, set.preimage_preimage],
  refine set.subset.antisymm _ _; intros x h,
  { refine ⟨pi_subtype B x, h, _⟩, ext ⟨⟨_, _⟩, _⟩, refl },
  { obtain ⟨_, h', h⟩ := h,
    change pi_subtype B x ∈ sb,
    convert h',
    refine pi_subtype_ext'.mpr _,
    rintro ⟨_, hi⟩,
    exact (congr_fun h ⟨⟨_, hba hi⟩, _⟩).symm }
end

lemma pi_unsubtype_union_img_inter₁₂ {α : Type*} {β : α → Type*} (A : set α) (B : set α)
  (a : set (Π i : A, β i)) (b : set (Π i : B, β i)) :
  >[] (>₁[] a ∩ >₂[] b) = >[] a ∩ >[] b :=
begin
  simp_rw pi_unsubtype_img,
  rw set.preimage_inter,
  simp_rw pi_unsubtype_union_img₁,
  simp_rw pi_unsubtype_union_img₂,
  refine congr (congr_arg has_inter.inter _) _,
  exact (pi_subtype_subtype_subset (set.subset_union_left A B) _).symm,
  exact (pi_subtype_subtype_subset (set.subset_union_right A B) _).symm
end

end probability_theory
