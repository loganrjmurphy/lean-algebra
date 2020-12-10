import definitions subgroups basic tactic
open function tactic 

universe u

namespace Algebra

variables (G H : Type u) [group G] [group H]

structure hom := 
(f : G → H)
(prsv : ∀ a b : G, f(a + b) = f a + f b)

def iso : Type* := {φ : hom G H // bijective φ.f}

def image (φ : hom G H) : set H:=
set.range φ.f 

lemma hom_id_to_id (φ : hom G H) : φ.1 (0 : G) = (0 : H) := 
begin 
  cases φ with f H, simp,
  replace H := H 0 0,
  rw group.ident_r at H,
  nth_rewrite 0   ← add_zero (f 0) at H,
  symmetry,
  apply group.cancel_left (f 0) 0 (f 0), exact H,
end 

lemma hom_img_has_ident (φ : hom G H) : (0 : H) ∈ (image G H φ) := 
begin
  rw image, simp, use 0, exact hom_id_to_id G H φ,
end 

lemma hom_image_subgroup (φ : hom G H) : subgroup H := 
{ carrier := (image G H φ),
  has_ident := hom_img_has_ident G H φ,
  closure := 
  begin 
    intros a b H1 H2,
    cases H1 with g₁ H1,
    cases H2 with g₂ H2,
    rw image, simp, use (g₁ + g₂), 
    rw [φ.2, H1, H2]
  end ,
  has_inv := 
  begin
    intros a H1, simp at *,
    cases H1 with w H1,
    use (-w),
     
  end }

end Algebra 