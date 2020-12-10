import definitions subgroups basic 

namespace Algebra

namespace coset 

variables {G : Type} [group G] {K : subgroup G} 
{a b g h: G}

def left_coset (g : G) (H : subgroup G) : set G := 
{g' | ∃ h ∈ H,  g + h = g'}

def right_coset (g : G) (H : subgroup G) : set G := 
{g' | ∃ h ∈ H,  h + g = g'}

def in_left_coset {g₁ g₂ g₃: G} {H : subgroup G} (h₁ : g₃ ∈ H) (h₂ : g₁ + g₃ = g₂) : g₂ ∈ left_coset g₁ H := 
by {rw left_coset, simp, exact ⟨g₃, h₁,h₂⟩}


def left_cosets_exists_iff_exists
(H' : left_coset a K = left_coset b K) : 
(∃ (h : G), h ∈ K ∧ a + h = g) → (∃ (h : G), h ∈ K ∧ b + h = g) :=  begin rintros ⟨w, H1, H2⟩,
    have H3: g ∈ left_coset a K, 
      from in_left_coset H1 H2,
    have H4: g ∈ left_coset b K, 
      by {rw ← H', assumption},
    cases H4 with w' H4, cases H4 with H5 H4,
    use w', split, assumption, assumption
end 

def left_cosets_eq_iff {a b : G} {K : subgroup G}: 
  left_coset a K = left_coset b K ↔ 
   ∀ g : G, 
      (∃ h : G, h ∈ K ∧ a + h = g) ↔ 
      (∃ h : G, h ∈ K ∧  b + h = g) := 
begin 
  split, 
  { intro H', intro g, split,
    {apply left_cosets_exists_iff_exists H'},
    {apply left_cosets_exists_iff_exists H'.symm}},
  { intro H', repeat {rw left_coset},
    ext, simp, split,
    {   intro H1,
        replace H' := H' x,
        apply H'.mp, exact H1,},
    { intro H1, replace H' := H' x, apply H'.mpr, exact H1,}}
end 


variables {g₁ g₂ : G}

lemma right_inv_cosets_eq_of_left_cosets_eq (H : left_coset a K = left_coset b K) :
  right_coset (-a) K = right_coset (-b) K := 
begin  
  replace H := left_cosets_eq_iff.mp H,
  ext,
  split, 
  { 
    intro H,
  }
end 


end coset 
end Algebra 