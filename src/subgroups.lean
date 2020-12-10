import definitions basic 
universe u 

namespace Algebra 

variables {M : Type*} [monoid M] {s : set M}
variables {A : Type*} [add_monoid A] {t : set A}

structure submonoid (M : Type*) [monoid M] :=
(carrier : set M)
(has_ident : (0 : M) ∈ carrier)
(closure {a b} : a ∈ carrier → b ∈ carrier → a + b ∈ carrier)


namespace submonoid

instance : has_coe (submonoid M) (set M) := ⟨submonoid.carrier⟩

instance : has_mem M (submonoid M) := ⟨λ m S, m ∈ (S:set M)⟩

instance : has_coe_to_sort (submonoid M) := ⟨Type*, λ S, {x : M // x ∈ S}⟩

@[simp]
lemma mem_carrier {s : submonoid M} {x : M} : x ∈ s.carrier ↔ x ∈ s := iff.rfl

@[simp]
lemma mem_coe {S : submonoid M} {m : M} : m ∈ (S : set M) ↔ m ∈ S := iff.rfl

@[simp]
lemma coe_coe (s : submonoid M) : ↥(s : set M) = s := rfl

protected lemma «exists» {s : submonoid M} {p : s → Prop} :
  (∃ x : s, p x) ↔ ∃ x ∈ s, p ⟨x, ‹x ∈ s›⟩ :=
set_coe.exists

protected lemma «forall» {s : submonoid M} {p : s → Prop} :
  (∀ x : s, p x) ↔ ∀ x ∈ s, p ⟨x, ‹x ∈ s›⟩ :=
set_coe.forall

/-- Two submonoids are equal if the underlying subsets are equal. -/
theorem ext' ⦃S T : submonoid M⦄ (h : (S : set M) = T) : S = T :=
by cases S; cases T; congr'

@[ext]
theorem ext {S T : submonoid M}(h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := 
ext' $ set.ext h

variable (S : submonoid M) 

lemma ident : (0 : M) ∈ S := S.has_ident    
lemma subset_closure {x y : M} : x ∈ S → y ∈ S → x + y ∈ S := submonoid.closure S

end submonoid 

structure subgroup (G : Type*) [group G] extends submonoid G :=
(has_inv {x} : x ∈ carrier → -x ∈ carrier)

instance (G : Type u) [group G] : has_mem G (subgroup G) := 
{ mem := λ g H,  g ∈ H.carrier }

instance (G : Type u) [group G] : has_coe_to_sort (subgroup G) := ⟨Type u, λ S, {x : G // x ∈ S}⟩


namespace subgroup

variables {G : Type u} [group G] (H : subgroup G)

instance is_submonoid : has_coe (subgroup G) (submonoid G) := {coe := λ G, { carrier := G.carrier,
  has_ident := G.has_ident,
  closure := G.closure}}

instance : has_coe (subgroup G) (set G) := {coe := λ G, G.carrier}

instance : has_add H := 
{add := by 
 {rintros ⟨a, Ha⟩ ⟨b,Hb⟩,
  use (a+b), apply H.closure, assumption, assumption}} 

lemma associative : ∀ a b c : H, a + b + c = a + (b + c) := 
begin
  rintros ⟨a, h₁⟩ ⟨b, h₂⟩ ⟨c,h₃⟩,
  unfold has_add.add,
  rw subtype.mk_eq_mk,
  rw group.associative
end 

end subgroup 

def has_identity (G : Type u) [group G] (H : subgroup G) : Prop := (0 : G) ∈ H

namespace subgroup

variables (G : Type u) [group G] (H : subgroup G) 

theorem has_identity : has_identity G H := by {rw has_identity, exact H.has_ident} 

-- A subgroup is itself a group 

lemma is_group (H : subgroup G) : group H := 
{ add := has_add.add,
  assoc := subgroup.associative H,
  zero := 
  by {have := subgroup.has_identity G H, use 0, assumption},
  ident_l := 
  by {dsimp,
      unfold has_add.add,  tidy},
  ident_r :=  
  by {dsimp,
      unfold has_add.add,  tidy},
  neg := λ ⟨a,h⟩, 
  by {have := H.has_inv h, use (-a), assumption} ,
  inv_l := λ ⟨a,h⟩,
  by { unfold has_add.add, simp,} 
}

end subgroup

def is_subgroup_of (G : Type u) [group G] (H : subgroup G) : Prop := Algebra.has_identity G H ∧ (∀ h₁ h₂ : G, h₁ ∈ H → h₂ ∈ H → h₁ + h₂ ∈ H) ∧ (∀ g : G, g ∈ H → (-g) ∈ H)  

namespace subgroup


variables (G : Type u) [group G] (H : subgroup G) 


-- obviously, every [subgroup G] is a subgroup of G 


lemma is_subgroup_of : is_subgroup_of G H :=
⟨subgroup.has_identity G H,H.closure,H.has_inv⟩  


-- Every group G is a subgroup of G 

def self : subgroup G := 
{ carrier := set.univ,
  has_ident := dec_trivial,
  closure := λ a b , by dec_trivial,
  has_inv := λ g, by dec_trivial}

lemma self.is_subgroup_of : Algebra.is_subgroup_of 
G 
(subgroup.self G) := 
begin 
  split, exact has_identity G (self G),
  split,
  exact (self G).closure,
  exact (self G).has_inv,
end 


-- Particular subgroups 

def intersection (K₁ K₂ : subgroup G) : subgroup G := 
{ carrier := K₁ ∩ K₂,
  has_ident := 
  by {simp, split,
      exact K₁.has_ident, exact K₂.has_ident},
  closure := 
  by {
  intros a b H1 H2, 
  cases H1 with L1 R1,
  cases H2 with L2 R2,
  simp, split, 
  apply K₁.closure, assumption, assumption,
  apply K₂.closure, assumption, assumption},
  has_inv := 
  by {
  intros a H, simp at *, cases H with L R,
  split,
  exact K₁.has_inv L,
  exact K₂.has_inv R,
  }
}

def center_of (G : Type u) [group G] : set G := {x : G | ∀ g : G, g + x = x + g}

lemma center_closure : ∀ a b : G, a ∈ center_of G → b ∈ center_of G → a + b ∈ center_of G := 
begin 
  intros a b H1 H2, rw center_of,
  simp at *, intro g, rw group.associative,
  replace H2 := H2 g, replace H1 := H1 g,
  rw [← H2, ← group.associative, H1,  group.associative]
end 

lemma center_inv : ∀ x : G, x ∈ center_of G → -x ∈ center_of G := begin 
  intros a, rw center_of, simp, intros H1 g,
  obtain H2 := H1 g, 
  replace H2 := group.congr_l (-a) H2,
  replace H2 := group.congr_r (-a) H2,
  rw [← group.associative, ← (H1 g),
   group.associative, group.inv_r, group.ident_r] at H2,
  rw (H1 g) at H2,
  rw [← group.associative ,  group.inv_l,group.ident_l] at H2,
  symmetry, exact H2,
end 


def center : subgroup G := { 
  carrier := center_of G,
  has_ident := 
    by {rw center_of, simp},
  closure := center_closure G,
  has_inv := center_inv G
}

end subgroup 

end Algebra 
