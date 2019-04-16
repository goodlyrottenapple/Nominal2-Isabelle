theory Name_Exec
imports "../../Nominal2"
begin

atom_decl name

definition Name :: "nat \<Rightarrow> name" where "Name n = Abs_name (Atom (Sort ''Name_Exec.name'' []) n)"

definition "nat_of_name n = nat_of (Rep_name n)"

code_datatype Name

definition [code]: "N0 = Name 0"
definition [code]: "N1 = Name 1"
definition [code]: "N2 = Name 2"

instantiation name :: equal begin

definition equal_name_def: "equal_name a b \<longleftrightarrow> nat_of_name a = nat_of_name b"

instance
  by default
    (metis (lifting) Rep_name_inject atom_components_eq_iff atom_name_def equal_name_def nat_of_name_def sort_of_atom_eq)

end

lemma [simp]: "nat_of_name (Name n) = n"
  unfolding nat_of_name_def Name_def
  by (simp add: Abs_name_inverse)

lemma equal_name_code [code]: "(equal_class.equal (Name x) (Name y)) \<longleftrightarrow> (x = y)"
  by (auto simp add: equal_name_def)

lemma atom_name_code[code]:
  "atom (Name n) = Atom (Sort ''Name_Exec.name'' []) n"
  by (simp add: Abs_name_inject[symmetric] Name_def)
     (simp add: atom_name_def Rep_name_inverse)

lemma permute_name_code[code]: "p \<bullet> n = Name (nat_of (p \<bullet> (atom n)))"
  apply (simp add: atom_eqvt)
  apply (simp add: atom_name_def Name_def)
  by (metis Rep_name_inverse atom_name_def atom_name_sort nat_of.simps sort_of.simps atom.exhaust)

(*
Test:
definition "t \<longleftrightarrow> 0 = (N0 \<leftrightarrow> N1)"

export_code t in SML

value "(N0 \<leftrightarrow> N1) + (N1 \<leftrightarrow> N0) = 0"
*)

end



