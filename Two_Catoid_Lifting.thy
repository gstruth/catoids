(* 
Title: Lifting 2-Catoids to Powerset 2-Quantales
Author: Georg Struth
Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section \<open>Lifting 2-Catoids to Powerset 2-Quantales\<close>

theory Two_Catoid_Lifting
  imports Two_Catoid Two_Quantale

begin

instantiation set :: (catoid) monoid_mult

begin

definition one_set :: "'a set" where
  "1 = sfix"

definition times_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where 
  "X * Y = X \<star> Y"

instance
  apply intro_classes
  unfolding times_set_def one_set_def
    apply (simp add: conv_assoc)
  using stopp.conv_unt apply blast
  by (metis stfix_set stopp.conv_uns)

end

instantiation set :: (catoid) dioid

begin

definition zero_set :: "'a set" where
  "zero_set = {}"

definition plus_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "X + Y = X \<union> Y"

instance
  by (intro_classes, auto simp: plus_set_def sup_assoc sup_commute zero_set_def sup.absorb_iff2 psubset_eq times_set_def conv_exp)

end

instantiation set :: (catoid) quantale

begin

instance
  by (intro_classes, auto simp: times_set_def conv_exp)

end

(*
instantiation set :: (local_lr_multisemigroup) modal_semiring

begin

definition d_set :: "'a set \<Rightarrow> 'a set" where
  "d X = L X"

definition cod_set :: "'a set \<Rightarrow> 'a set" where
 "codomain_semiring_class.cod X = R X"

instance
  apply intro_classes
             apply (auto simp: cod_set_def times_set_def image_Un plus_set_def lr_fix_set lropp.L_subid zero_set_def d_set_def lropp.R_subid)
  using lropp.LR_im lropp.rfix_im one_set_def apply blast
  using lropp.rfix_im one_set_def by blast

end
*)

instantiation set :: (local_catoid) modal_quantale

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

instantiation set :: (local_two_catoid) globular_2_quantale

begin

definition dom\<^sub>0_set :: "'a set \<Rightarrow> 'a set" where
 "dom\<^sub>0 X = Src\<^sub>0 X"

definition cod\<^sub>0_set :: "'a set \<Rightarrow> 'a set" where
  "cod\<^sub>0 X = Tgt\<^sub>0 X"

definition comp0_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where 
  "X \<cdot>\<^sub>0 Y = X *\<^sub>0 Y" 

definition id0_set :: "'a set"
  where "1\<^sub>0 = s0fix"

definition dom\<^sub>1_set :: "'a set \<Rightarrow> 'a set" where
  "dom\<^sub>1 X = Src\<^sub>1 X"

definition cod\<^sub>1_set :: "'a set \<Rightarrow> 'a set" where
  "cod\<^sub>1 X = Tgt\<^sub>1 X"

definition comp1_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where 
  "X \<cdot>\<^sub>1 Y = X *\<^sub>1 Y" 

definition id1_set :: "'a set" where
  "1\<^sub>1 = t1fix"

instance
  apply intro_classes
  unfolding comp0_set_def dom\<^sub>0_set_def cod\<^sub>0_set_def id0_set_def comp1_set_def dom\<^sub>1_set_def cod\<^sub>1_set_def id1_set_def
                      apply (simp add: msg0.conv_assoc)
  using stmm0.stopp.stopp.conv_uns apply blast
                      apply (metis stmm0.stopp.stopp.conv_unt stmm0.stopp.stopp.st_fix_set)
                      apply (smt (verit, ccfv_SIG) Collect_cong image_def stmm0.stopp.conv_distr)
                      apply (smt (z3) Collect_cong image_def multimagma.conv_distr)
                      apply simp+
                      apply (simp add: image_Un)
  using stmm0.stopp.stopp.Tgt_subid stmm0.stopp.stopp.st_fix_set apply blast
                      apply force
                      apply simp+
                      apply (simp add: image_Un)
  using stmm0.stopp.stopp.Src_subid apply blast
                      apply force
                      apply simp+
                      apply (simp add: msg1.conv_assoc)
                      apply (metis stmm1.stopp.stopp.conv_uns stmm1.stopp.stopp.st_fix_set)
  using stmm1.stopp.stopp.conv_unt apply blast
                     apply (smt (verit, best) Collect_cong image_def multimagma.conv_distl)
                    apply (smt (verit) Collect_cong image_def multimagma.conv_distr)
                   apply simp+
                 apply (simp add: image_Un)
  using stmm1.stopp.stopp.Tgt_subid apply blast
               apply simp+
            apply (simp add: image_Un)
           apply force
  by (simp_all add: image_Un interchange_lifting Src1_hom codcomp Src0_weak_hom Tgt0_weak_hom)

end

end










 







 







