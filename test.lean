import measure_theory.measure.measure_space

open set

theorem set.image_inter_on' {α β} {f : α → β} {s t : set α}
  (h : ∀x∈s, ∀y∈t, x ∉ s ∩ t → y ∉ s ∩ t → f x = f y → x = y) :
  f '' s ∩ f '' t = f '' (s ∩ t) :=
subset.antisymm
  (assume b ⟨⟨a₁, ha₁, h₁⟩, ⟨a₂, ha₂, h₂⟩⟩,
    begin
      by_cases hs : a₁ ∈ s ∩ t ∨ a₂ ∈ s ∩ t,
      { cases hs;
        have := mem_image_of_mem f hs,
        rwa h₁.symm, rwa h₂.symm },
      have := not_or_distrib.mp hs,
      have : a₁ = a₂ := h _ ha₁ _ ha₂ this.1 this.2 (by simp *),
      exact ⟨a₁, ⟨ha₁, this.symm ▸ ha₂⟩, h₁⟩
    end)
  (image_inter_subset _ _ _)

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
