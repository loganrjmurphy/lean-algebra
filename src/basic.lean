import definitions tactic
universe u 

namespace Algebra 

namespace group 

variables {G : Type u} [group G]

lemma group_nonempty : nonempty G := ⟨0⟩ 

def is_ident (e : G) : Prop := ∀ g : G, e + g = g ∧ g + e = g

lemma id_unique : ∀ e : G, is_ident e → e = 0 := 
begin 
  intros e H,
  rw is_ident at H, cases H 0 with H1 H2,
  simp at H1, 
  assumption
end 

def is_inv (g g' : G) : Prop := g + g' = 0 ∧ g' + g = 0

lemma inv_unique : ∀ g g': G, is_inv g g' →  (-g) = g':= 
begin 
  intros a b H, cases H with H1 H2,
  have H3 : b + 0 = b, from group.ident_r,
  have H4 : b + (a + (-a)) = b, by {rwa ← group.inv_r at H3},
  rw ← group.associative at H4,
  rwa [H2, group.ident_l] at H4,
end 

@[simp]
lemma op_inv : ∀ a b : G, -(a + b) = (-b) + (-a) := 
begin 
  intros a b,
  have H1 : (a + b) + ((-b) + (-a)) = 0, 
  by {rw ← group.associative, simp,},
  have H2 : (-b) + (-a) + (a + b) = 0, 
  by { rw ← group.associative, rw  @group.associative G _inst_1 (-b) (-a) a, 
       rw group.inv_l, simp,},
  have H3 : is_inv (a + b) (-b + -a) := ⟨H1,H2⟩,
  exact inv_unique (a + b) (-b + -a) H3,
end  

def congr_l {b c : G} (a : G) (h : b = c) : a + b = a + c := 
congr (refl (λ g, a + g)) h 

def congr_r {b c : G} (a : G) (h : b = c) :  b + a = c + a:= 
@congr G G (λ g, g + a) (λ g, g + a) b c (by refl) h 

lemma cancel_right : ∀ a b c : G, b + a = c + a →  b = c := 
begin 
  intros a b c H,
  have : b + a + (-a) = c + a + (-a) := congr_r (-a) H,
  simp at this, exact this
end  

lemma cancel_left : ∀ a b c : G, a + b = a + c → b = c := 
begin 
  intros a b c H,
  have :  (-a) + (a + b) = (-a) + (a + c) := congr_l (-a) H,
  simp at this, exact this
end  

lemma square_ident_imp_self_inv (G : Type u) [group G] : ∀ g : G, g ↟ 2 = 0 → (-g = g) := 
begin
  intro g, repeat {rw pow}, rw group.ident_r, 
  intro H, apply inv_unique, exact ⟨H,H⟩
end 

lemma square_ident_imp_abelian : (∀ g : G, g ↟ 2 = 0) → abelian G :=
begin 
  intros H1 a b,
  obtain H2 := square_ident_imp_self_inv G a (H1 a),
  obtain H3 := square_ident_imp_self_inv G b (H1 b),
  obtain H4 := square_ident_imp_self_inv G (a + b) (H1 (a + b)), 
  simp at H4,  
  rw [H2,H3] at H4, symmetry, exact H4,
end 



end group




end Algebra 