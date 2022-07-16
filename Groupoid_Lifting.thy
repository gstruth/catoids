(* 
Title: Lifting Groupoids to Distributive Dedekind Quantales
Author: Georg Struth
Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section \<open>Lifting Groupoids to Distributive Dedekind Quantales\<close>

theory Groupoid_Lifting
  imports Groupoid Quantale_conv

begin

instantiation set :: (groupoid) monoid_mult

begin

definition one_set :: "'a set" where
  "1 = sfix"

definition times_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where 
  "X \<cdot> Y = X \<star> Y"

instance
  apply intro_classes
  unfolding times_set_def one_set_def
    apply (simp add: conv_assoc)
  using stopp.conv_unt apply blast
  by (metis stfix_set stopp.conv_uns) 

end

instantiation set :: (groupoid) dioid

begin

definition zero_set :: "'a set" where
  "zero_set = {}"

definition plus_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "X + Y = X \<union> Y"

instance
  by (intro_classes, auto simp: plus_set_def sup_assoc sup_commute zero_set_def sup.absorb_iff2 psubset_eq times_set_def conv_exp)

end

instantiation set :: (groupoid) quantale

begin

instance
  by (intro_classes, auto simp: times_set_def conv_exp)

end

instantiation set :: (groupoid) modal_quantale

begin

definition dom_set :: "'a set \<Rightarrow> 'a set" where
  "dom X = Src X"

definition cod_set :: "'a set \<Rightarrow> 'a set" where
 "cod X = Tgt X"

instance
  apply intro_classes
  unfolding dom_set_def cod_set_def times_set_def one_set_def     
  apply simp+
  apply (simp add: image_Un)
  using st_fix_set stopp.Src_subid apply blast
  apply simp+
  apply (simp add: image_Un)
  using stopp.Tgt_subid apply blast
  by auto

end

instantiation set :: (groupoid) distributive_dedekind_quantale

begin

definition invol_set :: "'a set \<Rightarrow> 'a set" where
  "invol = Inv"

instance
  by (intro_classes, simp_all add: invol_set_def Inv_contrav times_set_def st_mgpd.Inv_Un groupoid_class.modular_law)

end

end










 







 







