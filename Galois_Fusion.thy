(* 
Title: Fusion Laws
Author: Georg Struth
Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section \<open>Galois Connection and Fixpoint Fusion\<close>

theory Galois_Fusion
  imports "Two_KA"

begin

text \<open>This comes from an AFP entry for lattices.\<close>

unbundle "lattice_syntax"

definition adj :: "('a::ord \<Rightarrow> 'b::ord) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool" (infixl "\<stileturn>" 70) where 
  "(f \<stileturn> g) = (\<forall>x y. (f x \<le> y) = (x \<le> g y))"

definition "ladj (g::'a::Inf \<Rightarrow> 'b::ord) = (\<lambda>x. \<Sqinter>{y. x \<le> g y})"

definition "radj (f::'a::Sup \<Rightarrow> 'b::ord)  = (\<lambda>y. \<Squnion>{x. f x \<le> y})"

lemma adj_iso1: "f \<stileturn> g \<Longrightarrow> mono f"
  unfolding adj_def mono_def by (meson dual_order.refl dual_order.trans) 

lemma adj_iso2: "f \<stileturn> g \<Longrightarrow> mono g"
  unfolding adj_def mono_def by (meson dual_order.refl dual_order.trans) 

lemma adj_comp: "f \<stileturn> g \<Longrightarrow> adj h k \<Longrightarrow> (f \<circ> h) \<stileturn> (k \<circ> g)"
  by (simp add: adj_def)

lemma adj_cancel1: 
  fixes f :: "'a::preorder \<Rightarrow> 'b::ord"
  shows "f \<stileturn> g \<Longrightarrow> f \<circ> g \<le> id"
  by (simp add: adj_def le_funI)

lemma adj_cancel2: 
  fixes f :: "'a::ord \<Rightarrow> 'b::preorder"
  shows "f \<stileturn> g \<Longrightarrow> id \<le> g \<circ> f"
  by (simp add: adj_def eq_iff le_funI)

lemma adj_prop: 
  fixes f :: "'a::preorder \<Rightarrow>'a"
  shows "f \<stileturn> g \<Longrightarrow> f \<circ> g \<le> g \<circ> f"
  using adj_cancel1 adj_cancel2 order_trans by blast

lemma adj_cancel_eq1: 
  fixes f :: "'a::preorder \<Rightarrow> 'b::order"
  shows "f \<stileturn> g \<Longrightarrow> f \<circ> g \<circ> f = f"
  unfolding adj_def comp_def fun_eq_iff by (meson eq_iff order_refl order_trans)

lemma adj_cancel_eq2: 
  fixes f :: "'a::order \<Rightarrow> 'b::preorder"
  shows "f \<stileturn> g \<Longrightarrow> g \<circ> f \<circ> g = g"
  unfolding adj_def comp_def fun_eq_iff by (meson eq_iff order_refl order_trans) 

lemma adj_idem1: 
  fixes f :: "'a::preorder \<Rightarrow> 'b::order"
  shows "f \<stileturn> g \<Longrightarrow> (f \<circ> g) \<circ> (f \<circ> g) = f \<circ> g"
  by (simp add: adj_cancel_eq1 rewriteL_comp_comp)

lemma adj_idem2: 
  fixes f :: "'a::order \<Rightarrow> 'b::preorder"
  shows "f \<stileturn> g \<Longrightarrow> (g \<circ> f) \<circ> (g \<circ> f) = g \<circ> f"
  by (simp add: adj_cancel_eq2 rewriteL_comp_comp)

lemma adj_iso3: 
  fixes f :: "'a::order \<Rightarrow> 'b::order"
  shows "f \<stileturn> g \<Longrightarrow> mono (f \<circ> g)"
  by (simp add: adj_iso1 adj_iso2 monoD monoI)

lemma adj_iso4: 
  fixes f :: "'a::order \<Rightarrow> 'b::order"
  shows "f \<stileturn> g \<Longrightarrow> mono (g \<circ> f)"
  by (simp add: adj_iso1 adj_iso2 monoD monoI)

lemma adj_canc1: 
  fixes f :: "'a::order \<Rightarrow> 'b::ord"
  shows "f \<stileturn> g \<Longrightarrow> ((f \<circ> g) x = (f \<circ> g) y \<longrightarrow> g x = g y)"
  unfolding adj_def comp_def by (metis eq_iff)
 
lemma adj_canc2: 
  fixes f :: "'a::ord \<Rightarrow> 'b::order"
  shows "f \<stileturn> g \<Longrightarrow> ((g \<circ> f) x = (g \<circ> f) y \<longrightarrow> f x = f y)"
  unfolding adj_def comp_def by (metis eq_iff)

lemma adj_sur_inv: 
  fixes f :: "'a::preorder \<Rightarrow> 'b::order"
  shows "f \<stileturn> g \<Longrightarrow> ((surj f) = (f \<circ> g = id))"
  unfolding adj_def surj_def comp_def by (metis eq_id_iff eq_iff order_refl order_trans)

lemma adj_surj_inj: 
  fixes f :: "'a::order \<Rightarrow> 'b::order"
  shows "f \<stileturn> g \<Longrightarrow> ((surj f) = (inj g))"
  unfolding adj_def inj_def surj_def by (metis eq_iff order_trans)

lemma adj_inj_inv: 
  fixes f :: "'a::preorder \<Rightarrow> 'b::order"
  shows "f \<stileturn> g \<Longrightarrow> ((inj f) = (g \<circ> f = id))"
  by (metis adj_cancel_eq1 eq_id_iff inj_def o_apply)

lemma adj_inj_surj: 
  fixes f :: "'a::order \<Rightarrow> 'b::order" 
  shows "f \<stileturn> g \<Longrightarrow> ((inj f) = (surj g))"
  unfolding adj_def inj_def surj_def by (metis eq_iff order_trans)

lemma surj_id_the_inv: "surj f \<Longrightarrow> g \<circ> f = id \<Longrightarrow> g = the_inv f"
  by (metis comp_apply id_apply inj_on_id inj_on_imageI2 surj_fun_eq the_inv_f_f)

lemma inj_id_the_inv: "inj f \<Longrightarrow> f \<circ> g = id \<Longrightarrow> f = the_inv g"
  by (metis fun.set_map image_inv_f_f inj_imp_surj_inv surj_id surj_id_the_inv)

abbreviation Sup_pres :: "('a::Sup \<Rightarrow> 'b::Sup) \<Rightarrow> bool" where
  "Sup_pres f \<equiv> f \<circ> Sup = Sup \<circ> image f"

abbreviation Inf_pres :: "('a::Inf \<Rightarrow> 'b::Inf) \<Rightarrow> bool" where
  "Inf_pres f \<equiv> f \<circ> Inf = Inf \<circ> image f"

lemma radj_Inf_pres: 
  fixes g :: "'b::complete_lattice \<Rightarrow> 'a::complete_lattice"
  shows "(\<exists>f. f \<stileturn> g) \<Longrightarrow> Inf_pres g"
  apply (rule antisym, simp_all add: le_fun_def adj_def, safe)
  apply (meson INF_greatest Inf_lower dual_order.refl dual_order.trans)
  by (meson Inf_greatest dual_order.refl le_INF_iff)

lemma ladj_Sup_pres: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "(\<exists>g. f \<stileturn> g) \<Longrightarrow> Sup_pres f"
  apply (rule antisym, simp_all add: le_fun_def adj_def, safe)
  apply (metis SUP_upper Sup_least)
  by (meson SUP_least Sup_upper order_refl order_trans)

lemma radj_adj: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "f \<stileturn> g \<Longrightarrow> g = (radj f)"
  unfolding adj_def radj_def by (metis (mono_tags, lifting) cSup_eq_maximum eq_iff mem_Collect_eq)

lemma ladj_adj: 
  fixes g :: "'b::complete_lattice \<Rightarrow> 'a::complete_lattice" 
  shows "f \<stileturn> g \<Longrightarrow> f = (ladj g)"
  unfolding adj_def ladj_def by (metis (no_types, lifting) cInf_eq_minimum eq_iff mem_Collect_eq)

lemma Inf_subdistl_iso: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "f \<circ> Inf \<le> Inf \<circ> image f \<Longrightarrow> mono f"
  unfolding mono_def le_fun_def comp_def by (metis complete_lattice_class.le_INF_iff Inf_atLeast atLeast_iff)

lemma Inf_pres_radj_aux: 
  fixes g :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "Inf_pres g \<Longrightarrow> (ladj g) \<stileturn> g"
proof-
  assume a: "Inf_pres g"
  {fix x y
   assume b: "ladj g x \<le> y" 
   hence "g (ladj g x) \<le> g y"
    by (simp add: Inf_subdistl_iso a monoD)
  hence "\<Sqinter>{g y |y. x \<le> g y} \<le> g y"
    by (metis a comp_eq_dest_lhs setcompr_eq_image ladj_def)
  hence "x \<le> g y"
    using dual_order.trans le_Inf_iff by blast  
  hence "ladj g x \<le> y \<longrightarrow> x \<le> g y"
    by simp}
  thus ?thesis 
    unfolding adj_def ladj_def by (meson CollectI Inf_lower)
qed

lemma Sup_supdistl_iso: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "Sup \<circ> (`) f \<le> f \<circ> Sup \<Longrightarrow> mono f"
  unfolding mono_def le_fun_def comp_def by (metis complete_lattice_class.SUP_le_iff Sup_atMost atMost_iff)

lemma Sup_pres_ladj_aux: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice" 
  shows "Sup_pres f \<Longrightarrow> f \<stileturn> (radj f)"
proof-
  assume a: "Sup_pres f"
  {fix x y
   assume b: "x \<le> radj f y" 
   hence "f x \<le> f (radj f y)"
     by (simp add: Sup_supdistl_iso a monoD)
   hence "f x \<le> \<Squnion>{f x |x. f x \<le> y}"
     by (metis a comp_eq_dest_lhs setcompr_eq_image radj_def)
   hence "f x \<le> y"
     by (smt (verit, ccfv_SIG) Sup_eq_Inf le_Inf_iff mem_Collect_eq)
  hence "x \<le> radj f y \<longrightarrow> f x \<le> y"
    by simp}
  thus ?thesis 
    unfolding adj_def radj_def by (meson CollectI Sup_upper)
qed

lemma Inf_pres_radj: 
  fixes g :: "'b::complete_lattice \<Rightarrow> 'a::complete_lattice"
  shows "Inf_pres g \<Longrightarrow> (\<exists>f. f \<stileturn> g)"
  using Inf_pres_radj_aux by fastforce

lemma Sup_pres_ladj: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "Sup_pres f \<Longrightarrow> (\<exists>g. f \<stileturn> g)"
  using Sup_pres_ladj_aux by fastforce

lemma Inf_pres_upper_adj_eq: 
  fixes g :: "'b::complete_lattice \<Rightarrow> 'a::complete_lattice"
  shows "(Inf_pres g) = (\<exists>f. f \<stileturn> g)"
  using radj_Inf_pres Inf_pres_radj by blast

lemma Sup_pres_ladj_eq:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows  "(Sup_pres f) = (\<exists>g. f \<stileturn> g)"
  using Sup_pres_ladj ladj_Sup_pres by blast

definition Fix :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a set" where 
  "Fix f = {x. f x = x}"

lemma lfp_Fix:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  shows "mono f \<Longrightarrow> lfp f = \<Sqinter>(Fix f)"
  unfolding lfp_def Fix_def
  apply (rule antisym)
  apply (simp add: Collect_mono Inf_superset_mono)
  by (metis (mono_tags) Inf_lower lfp_def lfp_unfold mem_Collect_eq)

lemma gfp_Fix:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  shows "mono f \<Longrightarrow> gfp f = \<Squnion>(Fix f)"
  unfolding gfp_def Fix_def
  apply (rule antisym)
  apply (metis (mono_tags, lifting) Sup_mono def_gfp_unfold gfp_upperbound mem_Collect_eq)
  by (simp add: Collect_mono Sup_subset_mono)

lemma gfp_little_fusion:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  and g :: "'b::complete_lattice \<Rightarrow> 'b"
  assumes "mono f"
  assumes "h \<circ> f \<le> g \<circ> h"
  shows "h (gfp f) \<le> gfp g"
  by (metis assms(1) assms(2) comp_apply gfp_unfold gfp_upperbound le_funD)

lemma lfp_little_fusion:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  and g :: "'b::complete_lattice \<Rightarrow> 'b"
  assumes "mono f"
  assumes "g \<circ> h \<le> h \<circ> f"
  shows "lfp g \<le> h (lfp f)"
  by (metis assms(1) assms(2) comp_apply le_funD lfp_lowerbound lfp_unfold)

lemma gfp_fusion:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  and g :: "'b::complete_lattice \<Rightarrow> 'b"
  assumes "\<exists>f. f \<stileturn> h"
  and "mono f"
  and "mono g"
  and "h \<circ> f = g \<circ> h"
shows "h (gfp f) = gfp g"
  by (smt (verit, ccfv_threshold) adj_def assms(1) assms(2) assms(3) assms(4) comp_eq_elim gfp_eqI gfp_fixpoint gfp_upperbound monoD order_refl)

lemma lfp_fusion:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  and g :: "'b::complete_lattice \<Rightarrow> 'b"
  assumes "\<exists>f. h \<stileturn> f"
  and "mono f"
  and "mono g"
  and "h \<circ> f = g \<circ> h"
shows "h (lfp f) = lfp g"
  by (smt (verit, del_insts) adj_def assms(1) assms(2) assms(3) assms(4) comp_eq_elim dual_order.antisym lfp_lowerbound lfp_unfold monoD order_refl)

lemma gfp_fusion_inf_pres:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  and g :: "'b::complete_lattice \<Rightarrow> 'b"
  assumes "Inf_pres h"
  and "mono f"
  and "mono g"
  and "h \<circ> f = g \<circ> h"
  shows "h (gfp f) = gfp g"
  by (simp add: Inf_pres_radj assms gfp_fusion)

lemma lfp_fusion_sup_pres:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  and g :: "'b::complete_lattice \<Rightarrow> 'b"
  assumes "Sup_pres h"
  and "mono f"
  and "mono g"
  and "h \<circ> f = g \<circ> h"
shows "h (lfp f) = lfp g"
  by (simp add: Sup_pres_ladj assms lfp_fusion)

lemma k_adju: 
  fixes k :: "'a::order \<Rightarrow> 'b::complete_lattice"
  shows "\<forall>y.\<exists>F. (F::'b \<Rightarrow> 'a \<Rightarrow> 'b) \<stileturn> (\<lambda>k. k y)"
  by (force intro!: fun_eq_iff Inf_pres_radj)

lemma k_adju_var: "\<forall>y.\<exists>F.\<forall>x.\<forall>f::'a::order \<Rightarrow> 'b::complete_lattice. (F x \<le> f) = (x \<le> (\<lambda>k. k y) f)"
  using k_adju unfolding adj_def by blast

lemma gfp_fusion_var:
  fixes F :: "('a::order \<Rightarrow> 'b::complete_lattice) \<Rightarrow> 'a \<Rightarrow> 'b"
  and g :: "'b \<Rightarrow> 'b"
  assumes "mono F"
  and "mono g"
  and "\<forall>h. F h x = g (h x)"
shows "gfp F x = gfp g"
  by (metis (no_types, opaque_lifting) antisym assms(1) assms(2) assms(3) dual_order.refl gfp_unfold gfp_upperbound k_adju_var monoD)

end
