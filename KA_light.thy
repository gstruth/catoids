(* 
Title: A Light-Weight Component for Kleene Algebra
Author: Georg Struth
Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section \<open>Kleene Algebra Light\<close>

theory "KA_light"
  imports Main

begin

text \<open>Here is a light-weight component for Kleene algebra. It could eventually be replaced by the AFP entry.\<close>

subsection \<open>Semilattices\<close>

class sup_semilattice = comm_monoid_add + ord +
  assumes add_idem: "x + x = x"
  and order_def: "(x \<le> y) = (x + y = y)"
  and strict_order_def: "(x < y) = (x \<le> y \<and> x \<noteq> y)"

begin

subclass order 
  apply unfold_locales
     apply ( simp_all add: local.add_idem local.order_def local.strict_order_def add_commute)
   apply force
  by (metis add_assoc)

lemma zero_least: "0 \<le> x"
  by (simp add: local.order_def)

lemma add_isor: "x \<le> y \<Longrightarrow> x + z \<le> y + z"
  by (smt (verit, best) add_assoc add_commute local.add_idem local.order_def)

lemma add_iso: "x \<le> y \<Longrightarrow> x' \<le> y' \<Longrightarrow> x + x' \<le> y + y'"
  by (metis add_commute add_isor local.dual_order.trans)

lemma add_ubl: "x \<le> x + y"
  by (metis add_assoc local.add_idem local.order_def)

lemma add_ubr: "y \<le> x + y"
  using add_commute add_ubl by fastforce

lemma add_least: "x \<le> z \<Longrightarrow> y \<le> z \<Longrightarrow> x + y \<le> z"
  by (simp add: add_assoc local.order_def) 

lemma add_lub: "(x + y \<le> z) = (x \<le> z \<and> y \<le> z)"
  using add_least add_ubl add_ubr dual_order.trans by blast

end


subsection \<open>Dioids\<close>

text \<open>Dioids are multiplicatively idempotent semirings.\<close>

notation times (infixl "\<cdot>" 70)

class dioid =  monoid_mult + sup_semilattice +
  assumes distl: "x \<cdot> (y + z) = x \<cdot> y + x \<cdot> z"
  and distr: "(x + y) \<cdot> z = x \<cdot> z + y \<cdot> z"
  and annil [simp]: "0 \<cdot> x = 0"
  and annir [simp]: "x \<cdot> 0 = 0"

sublocale dioid \<subseteq> dd: dioid _ "\<lambda>x y. y \<cdot> x" _ _ _ _
  by (unfold_locales, simp_all add: mult_assoc local.distr local.distl)

class semiring_01 = semiring_0 + one +
  assumes onel [simp]: "1 \<cdot> x = x"
  and oner [simp]: "x \<cdot> 1 = x"

subclass (in dioid) semiring_01
  by (unfold_locales, simp_all add: local.distr local.distl)

text \<open>We do not use Isabelle's semirings because they require that 0 is not equal to 1.\<close>

lemma (in dioid) mult_isol: "x \<le> y \<Longrightarrow> z \<cdot> x \<le> z \<cdot> y"
  by (metis local.distl local.order_def)

lemma (in dioid) mult_isor: "x \<le> y \<Longrightarrow> x \<cdot> z \<le> y \<cdot> z"
  by (simp add: local.dd.mult_isol)

lemma (in dioid) mult_iso: "x \<le> y \<Longrightarrow> x' \<le> y' \<Longrightarrow> x \<cdot> x' \<le> y \<cdot> y'"
  using order_trans mult_isol mult_isor by blast

lemma (in dioid) power_inductl: "z + x \<cdot> y \<le> y \<Longrightarrow> x ^ i \<cdot> z \<le> y"
  apply (induct i)
   apply (simp add: local.add_lub)
  by (smt (verit, ccfv_SIG) dd.mult_assoc local.add_lub local.order_def local.power.power_Suc mult_isol)

lemma (in dioid) power_inductr: "z + y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> x ^ i \<le> y"
  apply (induct i)
   apply (simp add: local.add_lub)
  by (smt (verit, ccfv_SIG) dd.mult_assoc local.add_lub local.order_def local.power_Suc2 mult_isor)


subsection \<open>Kleene Algebras\<close>

class star_op =
  fixes star :: "'a \<Rightarrow> 'a" ("_\<^sup>\<star>" [101] 100)

class kleene_algebra = dioid + star_op +
  assumes star_unfoldl: "1 + x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"  
  and star_unfoldr: "1 + x\<^sup>\<star> \<cdot> x \<le> x\<^sup>\<star>"
  and star_inductl: "z + x \<cdot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<cdot> z \<le> y"
  and star_inductr: "z + y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y"

sublocale kleene_algebra \<subseteq> dka: kleene_algebra _ "\<lambda>x y. y \<cdot> x" _ _ _ _ _
  by (unfold_locales, simp_all add: local.star_unfoldr local.star_unfoldl local.star_inductr local.star_inductl)

lemma (in kleene_algebra) one_le_star: "1 \<le> x\<^sup>\<star>"
  using local.add_lub local.star_unfoldl by blast

lemma (in kleene_algebra) star_unfoldlr: "x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
  using add_lub star_unfoldl by simp

lemma (in kleene_algebra) star_unfoldrr: "x\<^sup>\<star> \<cdot> x \<le> x\<^sup>\<star>"
  by (simp add: local.dka.star_unfoldlr)

lemma (in kleene_algebra) star_infl: "x \<le> x\<^sup>\<star>"
  by (metis add_assoc local.distl local.mult_1_right local.order_def one_le_star star_unfoldlr) 

lemma (in kleene_algebra) star_power: "x ^ i \<le> x\<^sup>\<star>"
  apply (induct i)
  apply (simp add: one_le_star)
  by (metis local.mult_1_left local.power_inductr local.star_unfoldr)

lemma (in kleene_algebra) star_trans [simp]: "x\<^sup>\<star> \<cdot> x\<^sup>\<star> = x\<^sup>\<star>"
  apply (rule order.antisym)
  apply (simp add: local.add_least local.star_inductl local.star_unfoldlr)
  using local.mult_isol local.one_le_star by fastforce

lemma (in kleene_algebra) star_idem [simp]: "(x\<^sup>\<star>)\<^sup>\<star> = x\<^sup>\<star>"
  by (metis order.antisym local.eq_refl local.mult_1_right local.order_def local.star_inductl one_le_star star_infl star_trans) 

lemma (in kleene_algebra) star_unfoldl_eq [simp]: "1 + x \<cdot> x\<^sup>\<star> = x\<^sup>\<star>"
  by (metis local.add_iso order.antisym local.mult_1_right local.mult_isol local.order_refl local.star_inductl local.star_unfoldl)  

lemma (in kleene_algebra) star_unfoldr_eq: "1 + x\<^sup>\<star> \<cdot> x = x\<^sup>\<star>"
  by simp

lemma (in kleene_algebra) star_iso: "x \<le> y \<Longrightarrow> x\<^sup>\<star> \<le> y\<^sup>\<star>"
  by (smt (verit, ccfv_SIG) add_assoc local.add_ubl local.distr local.mult_1_right local.order_def local.star_inductl local.star_unfoldl_eq)

lemma (in kleene_algebra) star_slide: "(x \<cdot> y)\<^sup>\<star> \<cdot> x = x \<cdot> (y \<cdot> x)\<^sup>\<star>" 
  apply (rule order.antisym)
   apply (smt (verit, del_insts) local.add_lub local.mult_1_right local.mult_isol local.star_inductl mult_assoc one_le_star star_unfoldlr)
  by (smt (z3) local.distr local.eq_refl local.mult.semigroup_axioms local.mult_1_left local.star_inductr semigroup.assoc star_unfoldr_eq)

lemma (in kleene_algebra) star_denest: "(x + y)\<^sup>\<star> = x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>" 
 proof (rule order.antisym)
  have a: "1 \<le> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>"
    by (metis mult_1_right mult_isol order_trans one_le_star)
  have b: "x \<cdot> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>"
    by (simp add: mult_isor star_unfoldlr)
  have "y \<cdot> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star> \<le> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>"
    by (simp add: star_unfoldlr)
  also have  "\<dots> = 1 \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>"
    by simp
  also have "\<dots> \<le>  x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>"
    using mult_isor one_le_star by blast
  finally have "y \<cdot> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>".
  hence "1 + (x + y) \<cdot> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>"
    by (simp add: a b add_lub distr)
  thus  "(x + y)\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>"
    using mult_assoc star_inductl by fastforce
  have a: "x\<^sup>\<star> \<le> (x + y)\<^sup>\<star>"
    by (simp add: add_ubl star_iso)
  have "y \<le> (x + y)\<^sup>\<star>"
    using add_lub star_infl by blast
  hence "(y \<cdot> x\<^sup>\<star>)\<^sup>\<star> \<le> ((x + y)\<^sup>\<star> \<cdot> (x + y)\<^sup>\<star>)\<^sup>\<star>"
    using a mult_iso star_iso by blast
  also have "\<dots> = (x + y)\<^sup>\<star>"
    by simp
  finally have "(y \<cdot> x\<^sup>\<star>)\<^sup>\<star> \<le> (x + y)\<^sup>\<star>".
  hence "x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star> \<le> (x + y)\<^sup>\<star> \<cdot> (x + y)\<^sup>\<star>"
    using a mult_iso by blast
  also have "\<dots> \<le> (x + y)\<^sup>\<star>"
    by simp
  finally show "x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star> \<le> (x + y)\<^sup>\<star>".
qed

lemma (in kleene_algebra) star_subid: "x \<le> 1 \<Longrightarrow> x\<^sup>\<star> = 1"
  by (metis add_commute local.mult_1_left local.order.refl local.order_def local.star_inductr one_le_star)

lemma (in kleene_algebra) zero_star [simp]: "0\<^sup>\<star> = 1" 
  by (simp add: zero_least star_subid)

lemma (in kleene_algebra) one_star [simp]: "1\<^sup>\<star> = 1" 
  by (simp add: star_subid)

lemma (in kleene_algebra) star_sim1: "z \<cdot> x \<le> y \<cdot> z \<Longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y\<^sup>\<star> \<cdot> z"
  by (smt (verit) add_assoc add_commute local.dd.distl local.dd.distr local.dd.mult_assoc local.mult_1_left local.order_def local.star_inductr one_le_star star_unfoldr_eq)

lemma (in kleene_algebra) star_sim2: "x \<cdot> z \<le> z \<cdot> y \<Longrightarrow> x\<^sup>\<star> \<cdot> z  \<le> z \<cdot> y\<^sup>\<star>"
  by (simp add: local.dka.star_sim1)

lemma (in kleene_algebra) star_inductl_var: "x \<cdot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<cdot> y \<le> y"
  by (simp add: local.add_least local.star_inductl) 

lemma (in kleene_algebra) star_inductr_var: "y \<cdot> x \<le> y \<Longrightarrow> y \<cdot> x\<^sup>\<star> \<le> y"
  by (simp add: local.dka.star_inductl_var)

lemma (in kleene_algebra) church_rosser: "y\<^sup>\<star> \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<Longrightarrow> (x + y)\<^sup>\<star> = x\<^sup>\<star> \<cdot> y\<^sup>\<star>" 
  apply (rule order.antisym)
  apply (smt (verit, ccfv_SIG) add_commute local.mult_isor mult_assoc star_denest star_idem star_sim1 star_trans)
  by (metis local.add_ubl local.add_ubr local.mult_iso star_iso star_trans)

lemma (in kleene_algebra) power_sup: "((\<Sum>i=0..n. x^i) \<le> y) = (\<forall>i. 0 \<le> i \<and> i \<le> n \<longrightarrow> x^i \<le> y)"
  apply (induct n)
   apply simp
  using le_Suc_eq local.add_lub by force

lemma (in kleene_algebra) power_dist: "(\<Sum>i=0..n. x ^ i) \<cdot> x = (\<Sum>i=0..n. x ^ Suc i)"
  apply (induct n)
   apply simp
  using local.distr local.power_Suc2 local.sum.atLeast0_atMost_Suc by presburger 

lemma (in kleene_algebra) power_sum: "(\<Sum>i=0..n. x ^ Suc i) = (\<Sum>i=1..n. x ^ i) + x ^ Suc n"
  apply (induct n)
  by force+

lemma (in kleene_algebra) sum_star: "x\<^sup>\<star> = (x ^ Suc n)\<^sup>\<star> \<cdot> (\<Sum>i=0..n. x ^ i)"
proof (rule order.antisym)
  have "1 + (x ^ Suc n)\<^sup>\<star> \<cdot> (\<Sum>i=0..n. x ^ i) \<cdot> x = 1 + (x ^ Suc n)\<^sup>\<star> \<cdot> (\<Sum>i=0..n. x ^ Suc i)"
    using local.mult_assoc power_dist by presburger
  also have "\<dots> =  1 + (x ^ Suc n)\<^sup>\<star> \<cdot> (\<Sum>i=1..n. x ^ i) + (x ^ Suc n)\<^sup>\<star> \<cdot> x ^ Suc n"
    using local.add_assoc local.distl local.power_sum by presburger
  also have "\<dots> = (x ^ Suc n)\<^sup>\<star> \<cdot> (\<Sum>i=1..n. x ^ i) + (x ^ Suc n)\<^sup>\<star>"
    by (metis local.add.left_commute local.add_assoc star_unfoldr_eq)
  also have "\<dots> = (x ^ Suc n)\<^sup>\<star> \<cdot> (1 + (\<Sum>i=1..n. x ^ i))"
    using add_commute local.distl local.mult_1_right by presburger
  also have "\<dots> = (x ^ Suc n)\<^sup>\<star> \<cdot> (\<Sum>i=0..n. x ^ i)"
    by (simp add: local.sum.atLeast_Suc_atMost)
  finally show "x\<^sup>\<star> \<le> (x ^ Suc n)\<^sup>\<star> \<cdot> sum ((^) x) {0..n}"
    by (metis local.mult_1_left local.order_refl local.star_inductr)
next
  have a: "(x ^ Suc n)\<^sup>\<star> \<le> x\<^sup>\<star>"
    by (metis star_idem star_iso star_power)
  have "(\<Sum>i=0..n. x ^ i) \<le> x\<^sup>\<star>"
    using power_sup star_power by presburger
  thus "(x ^ Suc n)\<^sup>\<star> \<cdot> sum ((^) x) {0..n} \<le> x\<^sup>\<star>"
    by (metis a local.mult_iso star_trans)
qed

lemma (in kleene_algebra) newman_aux: "x\<^sup>\<star> \<cdot> y \<cdot> z\<^sup>\<star> = x\<^sup>\<star> \<cdot> y + x\<^sup>\<star> \<cdot> x \<cdot> y \<cdot> z \<cdot> z\<^sup>\<star> + y \<cdot> z\<^sup>\<star>"
  by (smt (z3) add_commute local.add.left_commute local.distl local.distr local.mult.monoid_axioms local.mult.semigroup_axioms local.mult_1_right local.order_def monoid.left_neutral one_le_star semigroup.assoc star_unfoldl_eq star_unfoldr_eq)

end
