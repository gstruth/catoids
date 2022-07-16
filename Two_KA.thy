(* 
Title: 2-Kleene Algebras
Author: Cameron Calk, Georg Struth
Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section \<open>2-Kleene algebras\<close>

theory "Two_KA"
  imports MKA_light

begin

text \<open>Here we develop (globular) 2-semigroups and (globular) 2-Kleene algebras. These should eventually
be extended to n-structures and omega-structures.\<close>

subsection \<open>Copies for 0-structures\<close>

class comp0_op =
  fixes comp0 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>\<^sub>0" 70)

class id0_op =
  fixes id0 :: "'a" ("1\<^sub>0")

class star0_op =
  fixes star0 :: "'a \<Rightarrow> 'a"

class dom0_op =
  fixes dom\<^sub>0 :: "'a \<Rightarrow> 'a"

class cod0_op =
  fixes cod\<^sub>0 :: "'a \<Rightarrow> 'a"

class monoid_mult0 = comp0_op + id0_op +
  assumes par_assoc0: "x \<cdot>\<^sub>0 (y \<cdot>\<^sub>0 z) = (x \<cdot>\<^sub>0 y) \<cdot>\<^sub>0 z"
  and comp0_unl: "1\<^sub>0 \<cdot>\<^sub>0 x = x" 
  and comp0_unr: "x \<cdot>\<^sub>0 1\<^sub>0 = x" 

class dioid0 = monoid_mult0 + sup_semilattice +
  assumes distl0: "x \<cdot>\<^sub>0 (y + z) = x \<cdot>\<^sub>0 y + x \<cdot>\<^sub>0 z"
  and distr0: "(x + y) \<cdot>\<^sub>0 z = x \<cdot>\<^sub>0 z + y \<cdot>\<^sub>0 z"
  and annil0: "0 \<cdot>\<^sub>0 x = 0"
  and annir0: "x \<cdot>\<^sub>0 0 = 0"

class kleene_algebra0 = dioid0 + star0_op +
  assumes star0_unfoldl: "1\<^sub>0 + x \<cdot>\<^sub>0 star0 x \<le> star0 x"  
  and star0_unfoldr: "1\<^sub>0 + star0 x \<cdot>\<^sub>0 x \<le> star0 x"
  and star0_inductl: "z + x \<cdot>\<^sub>0 y \<le> y \<Longrightarrow> star0 x \<cdot>\<^sub>0 z \<le> y"
  and star0_inductr: "z + y \<cdot>\<^sub>0 x \<le> y \<Longrightarrow> z \<cdot>\<^sub>0 star0 x \<le> y"

class domain_semiring0 = dioid0 + dom0_op +
  assumes d0_absorb: "x \<le> dom\<^sub>0 x \<cdot>\<^sub>0 x"
  and d0_local: "dom\<^sub>0 (x \<cdot>\<^sub>0 dom\<^sub>0 y) = dom\<^sub>0 (x \<cdot>\<^sub>0 y)"
  and d0_add: "dom\<^sub>0 (x + y) = dom\<^sub>0 x + dom\<^sub>0 y"
  and d0_subid: "dom\<^sub>0 x \<le> 1\<^sub>0"
  and d0_zero: "dom\<^sub>0 0 = 0"

class codomain_semiring0 = dioid0 + cod0_op +
  assumes cod0_absorb: "x \<le> x \<cdot>\<^sub>0 cod\<^sub>0 x" 
  and cod0_local: "cod\<^sub>0 (cod\<^sub>0 x \<cdot>\<^sub>0 y) = cod\<^sub>0 (x \<cdot>\<^sub>0 y)"
  and cod0_add: "cod\<^sub>0 (x + y) = cod\<^sub>0 x + cod\<^sub>0 y"
  and cod0_subid: "cod\<^sub>0 x \<le> 1\<^sub>0"
  and cod0_zero: "cod\<^sub>0 0 = 0"

class modal_semiring0 = domain_semiring0 + codomain_semiring0 +
  assumes dc_compat0: "dom\<^sub>0 (cod\<^sub>0 x) = cod\<^sub>0 x" 
  and cd_compat0:  "cod\<^sub>0 (dom\<^sub>0 x) = dom\<^sub>0 x" 

class modal_kleene_algebra0 = modal_semiring0 + kleene_algebra0

sublocale monoid_mult0 \<subseteq> mm0: monoid_mult "1\<^sub>0" "(\<cdot>\<^sub>0)"
  by (unfold_locales, simp_all add: local.par_assoc0 local.comp0_unl local.comp0_unr)

sublocale dioid0 \<subseteq> d0: dioid "1\<^sub>0" "(\<cdot>\<^sub>0)" _ _ _ _ 
  by (unfold_locales, simp_all add: local.distl0 local.distr0 annil0 annir0)

sublocale dioid0 \<subseteq> dd0: dioid0 _ _ _ _ "\<lambda>x y. y \<cdot>\<^sub>0 x" _
  by (unfold_locales, simp_all add: d0.dd.mult_assoc local.distr0 local.distl0)

sublocale kleene_algebra0 \<subseteq> k0: kleene_algebra "1\<^sub>0" "(\<cdot>\<^sub>0)" _ _ _ _ star0
  by ( unfold_locales, simp_all add: local.star0_unfoldl local.star0_unfoldr local.star0_inductl local.star0_inductr)

sublocale kleene_algebra0 \<subseteq> dk0: kleene_algebra0 _ _ _ _ "\<lambda>x y. y \<cdot>\<^sub>0 x" _ _
  by (unfold_locales, simp_all add: local.star0_inductr local.star0_inductl)

sublocale domain_semiring0 \<subseteq> dsr0: domain_semiring "1\<^sub>0" "(\<cdot>\<^sub>0)" _ _ _ _ "dom\<^sub>0"
  by (unfold_locales, simp_all add: local.d0_absorb local.d0_local local.d0_add local.d0_subid d0_zero)

sublocale codomain_semiring0 \<subseteq> csr0: codomain_semiring "1\<^sub>0" "(\<cdot>\<^sub>0)" _ _ _ _ "cod\<^sub>0"
  by (unfold_locales, simp_all add: local.cod0_absorb local.cod0_local local.cod0_add local.cod0_subid cod0_zero)

sublocale codomain_semiring0 \<subseteq> ds0dual: domain_semiring0 _ _ _ _ "\<lambda>x y. y \<cdot>\<^sub>0 x" _ cod\<^sub>0
  by (unfold_locales, simp_all add: local.cod0_absorb local.cod0_local local.cod0_add local.cod0_subid)

sublocale modal_semiring0 \<subseteq> msr0: modal_semiring "1\<^sub>0" "(\<cdot>\<^sub>0)" _ _ _ _ "cod\<^sub>0" "dom\<^sub>0"
  by (unfold_locales, simp_all add: local.dc_compat0 local.cd_compat0)

sublocale modal_semiring0 \<subseteq> msr0dual: modal_semiring0 "dom\<^sub>0" _ _ _ _ "\<lambda>x y. y \<cdot>\<^sub>0 x" _ "cod\<^sub>0"
  by (unfold_locales, simp_all add: local.d0_local local.d0_add local.d0_subid local.cd_compat0 local.dc_compat0)

sublocale modal_kleene_algebra0 \<subseteq> mka0: modal_kleene_algebra "1\<^sub>0" "(\<cdot>\<^sub>0)" _ _ _ _ star0 "cod\<^sub>0" "dom\<^sub>0"..

sublocale modal_kleene_algebra0 \<subseteq> mka0dual: modal_kleene_algebra0 _ _ _ _ "\<lambda>x y. y \<cdot>\<^sub>0 x" _ _ "dom\<^sub>0" "cod\<^sub>0"..


subsection \<open>Copies for 1-structures\<close>

class comp1_op =
  fixes comp1 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<cdot>\<^sub>1" 70)

class id1_op =
  fixes id1 :: "'a" ("1\<^sub>1")

class star1_op =
  fixes star1 :: "'a \<Rightarrow> 'a"

class dom1_op =
  fixes dom\<^sub>1 :: "'a \<Rightarrow> 'a"

class cod1_op =
  fixes cod\<^sub>1 :: "'a \<Rightarrow> 'a"

class monoid_mult1 = comp1_op + id1_op +
  assumes par_assoc1: "x \<cdot>\<^sub>1 (y \<cdot>\<^sub>1 z) = (x \<cdot>\<^sub>1 y) \<cdot>\<^sub>1 z"
  and comp1_unl: "1\<^sub>1 \<cdot>\<^sub>1 x = x" 
  and comp1_unr: "x \<cdot>\<^sub>1 1\<^sub>1 = x"

class dioid1 = monoid_mult1 + sup_semilattice +
  assumes distl1: "x \<cdot>\<^sub>1 (y + z) = x \<cdot>\<^sub>1 y + x \<cdot>\<^sub>1 z"
  and distr1: "(x + y) \<cdot>\<^sub>1 z = x \<cdot>\<^sub>1 z + y \<cdot>\<^sub>1 z"
  and annil1: "0 \<cdot>\<^sub>1 x = 0"
  and annir1: "x \<cdot>\<^sub>1 0 = 0"

class kleene_algebra1 = dioid1 + star1_op +
  assumes star1_unfoldl: "1\<^sub>1 + x \<cdot>\<^sub>1 star1 x \<le> star1 x"  
  and star1_unfoldr: "1\<^sub>1 + star1 x \<cdot>\<^sub>1 x \<le> star1 x"
  and star1_inductl: "z + x \<cdot>\<^sub>1 y \<le> y \<Longrightarrow> star1 x \<cdot>\<^sub>1 z \<le> y"
  and star1_inductr: "z + y \<cdot>\<^sub>1 x \<le> y \<Longrightarrow> z \<cdot>\<^sub>1 star1 x \<le> y"

class domain_semiring1 = dioid1 + dom1_op +
  assumes d1_absorb: "x \<le> dom\<^sub>1 x \<cdot>\<^sub>1 x"
  and d1_local: " dom\<^sub>1 (x \<cdot>\<^sub>1 dom\<^sub>1 y) = dom\<^sub>1 (x \<cdot>\<^sub>1 y)"
  and d1_add: "dom\<^sub>1 (x + y) = dom\<^sub>1 x + dom\<^sub>1 y"
  and d1_subid: "dom\<^sub>1 x \<le> 1\<^sub>1"
  and d1_zero: "dom\<^sub>1 0 = 0"

class codomain_semiring1 = dioid1 + cod1_op +
  assumes cod1_absorb: "x \<le> x \<cdot>\<^sub>1 cod\<^sub>1 x" 
  and cod1_local: "cod\<^sub>1 (cod\<^sub>1 x \<cdot>\<^sub>1 y) = cod\<^sub>1 (x \<cdot>\<^sub>1 y)"
  and cod1_add: "cod\<^sub>1 (x + y) = cod\<^sub>1 x + cod\<^sub>1 y"
  and cod1_subid: "cod\<^sub>1 x \<le> 1\<^sub>1"
  and cod1_zero: "cod\<^sub>1 0 = 0"

class modal_semiring1 = domain_semiring1 + codomain_semiring1 +
  assumes dc_compat1: "dom\<^sub>1 (cod\<^sub>1 x) = cod\<^sub>1 x" 
  and cd_compat1:  "cod\<^sub>1 (dom\<^sub>1 x) = dom\<^sub>1 x" 

class modal_kleene_algebra1 = modal_semiring1 + kleene_algebra1

sublocale  monoid_mult1 \<subseteq> mm1: monoid_mult "1\<^sub>1" "(\<cdot>\<^sub>1)"
  by (unfold_locales, simp_all add: local.par_assoc1 comp1_unl comp1_unr) 

sublocale  dioid1 \<subseteq>d1: dioid  "1\<^sub>1" "(\<cdot>\<^sub>1)" _ _ _ _
  by (unfold_locales, simp_all add: local.distl1 local.distr1 local.annil1 local.annir1)

sublocale  dioid1 \<subseteq> dd1: dioid1 _ _ _ _ "\<lambda>x y. y \<cdot>\<^sub>1 x"  "1\<^sub>1"
  by (unfold_locales, simp_all add: d1.dd.mult_assoc local.distr1 local.distl1)

sublocale kleene_algebra1 \<subseteq> k1: kleene_algebra "1\<^sub>1" "(\<cdot>\<^sub>1)" _ _ _ _ star1
  by ( unfold_locales, simp_all add: local.star1_unfoldl local.star1_unfoldr local.star1_inductl local.star1_inductr)

sublocale kleene_algebra1 \<subseteq> dk1: kleene_algebra1 _ _ _ _ "\<lambda>x y. y \<cdot>\<^sub>1 x" "1\<^sub>1" star1
  by (unfold_locales, simp_all add: local.star1_inductr local.star1_inductl)

sublocale domain_semiring1 \<subseteq> dsr1: domain_semiring "1\<^sub>1" "(\<cdot>\<^sub>1)" _ _ _ _ "dom\<^sub>1"
  by (unfold_locales, simp_all add: local.d1_absorb local.d1_local local.d1_add local.d1_subid d1_zero)

sublocale codomain_semiring1 \<subseteq> csr1: codomain_semiring "1\<^sub>1" "(\<cdot>\<^sub>1)" _ _ _ _ cod\<^sub>1
  by (unfold_locales, simp_all add: local.cod1_absorb local.cod1_local local.cod1_add local.cod1_subid cod1_zero)

sublocale codomain_semiring1 \<subseteq> ds1dual: domain_semiring1 _ _ _ _ "\<lambda>x y. y \<cdot>\<^sub>1 x" _ cod\<^sub>1
  by (unfold_locales, simp_all add: local.cod1_absorb local.cod1_local local.cod1_add local.cod1_subid)

sublocale modal_semiring1 \<subseteq> msr1: modal_semiring "1\<^sub>1" "(\<cdot>\<^sub>1)" _ _ _ _ "cod\<^sub>1" "dom\<^sub>1"
  by (unfold_locales, simp_all add: local.dc_compat1 local.cd_compat1)

sublocale modal_semiring1 \<subseteq> msr1dual: modal_semiring1  "dom\<^sub>1" _ _ _ _ "\<lambda>x y. y \<cdot>\<^sub>1 x" _ "cod\<^sub>1"
  by (unfold_locales, simp_all add: local.d1_local local.d1_add local.d1_subid local.cd_compat1 local.dc_compat1)

sublocale modal_kleene_algebra1 \<subseteq> mka1: modal_kleene_algebra "1\<^sub>1" "(\<cdot>\<^sub>1)" _ _ _ _ star1 "cod\<^sub>1" "dom\<^sub>1"..

sublocale modal_kleene_algebra1 \<subseteq> mka1dual: modal_kleene_algebra1 _ _ _ _ "\<lambda>x y. y \<cdot>\<^sub>1 x" _ _ "dom\<^sub>1" "cod\<^sub>1"..

subsection \<open>Globular 2-semirings\<close>

class globular_2_semiring = modal_semiring0 + modal_semiring1 +
  assumes interchange: "(w \<cdot>\<^sub>1 x) \<cdot>\<^sub>0 (y \<cdot>\<^sub>1 z) \<le> (w \<cdot>\<^sub>0 y) \<cdot>\<^sub>1 (x \<cdot>\<^sub>0 z)"
  and d1_hom [simp]: "dom\<^sub>1 (x \<cdot>\<^sub>0 y) = dom\<^sub>1 x \<cdot>\<^sub>0 dom\<^sub>1 y"
  and c1_hom [simp]: "cod\<^sub>1 (x \<cdot>\<^sub>0 y) = cod\<^sub>1 x \<cdot>\<^sub>0 cod\<^sub>1 y"
  and d0_weak_hom: "dom\<^sub>0 (x \<cdot>\<^sub>1 y) \<le> dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 y"
  and c0_weak_hom: "cod\<^sub>0 (x \<cdot>\<^sub>1 y) \<le> cod\<^sub>0 x \<cdot>\<^sub>1 cod\<^sub>0 y"
  and d1d0 [simp]: "dom\<^sub>1 (dom\<^sub>0 x) = dom\<^sub>0 x"

sublocale globular_2_semiring \<subseteq> tgsdual: globular_2_semiring "dom\<^sub>0" _ _ _ _ "\<lambda>x y. y \<cdot>\<^sub>0 x" _ "cod\<^sub>0"  "dom\<^sub>1" "\<lambda>x y. y \<cdot>\<^sub>1 x" _ "cod\<^sub>1"
  apply unfold_locales
       apply (simp_all add: local.interchange local.d0_weak_hom local.c0_weak_hom)
  by (metis local.cd_compat1 local.d1d0 local.dc_compat0)

lemma (in globular_2_semiring) c1d0 [simp]: "cod\<^sub>1 (dom\<^sub>0 x) = dom\<^sub>0 x"
proof-
  have "cod\<^sub>1 (dom\<^sub>0 x) = cod\<^sub>1 (dom\<^sub>1 (dom\<^sub>0 x))"
    by simp
  also have "\<dots> = dom\<^sub>1 (dom\<^sub>0 x)"
    using local.cd_compat1 by presburger
  also have "\<dots> = dom\<^sub>0 x"
    by simp
  finally show ?thesis.
qed

lemma (in globular_2_semiring) d1c0: "dom\<^sub>1 (cod\<^sub>0 x) = cod\<^sub>0 x"
  by simp

lemma (in globular_2_semiring) c1c0: "cod\<^sub>1 (cod\<^sub>0 x) = cod\<^sub>0 x"
  by simp

lemma (in globular_2_semiring) id1_comp0: "1\<^sub>1 \<cdot>\<^sub>0 1\<^sub>1 \<le> 1\<^sub>1"
proof-
  have "1\<^sub>1 \<cdot>\<^sub>0 1\<^sub>1 = dom\<^sub>1 1\<^sub>1 \<cdot>\<^sub>0 dom\<^sub>1 1\<^sub>1"
    by simp
  also have "\<dots> = dom\<^sub>1 (1\<^sub>1 \<cdot>\<^sub>0 1\<^sub>1)"
    by simp
  also have "\<dots> \<le> 1\<^sub>1"
    using local.d1_subid by blast
  finally show ?thesis.
qed

lemma (in globular_2_semiring) id1_comp0_eq [simp]: "1\<^sub>1 \<cdot>\<^sub>0 1\<^sub>1 = 1\<^sub>1"
proof-
  have "1\<^sub>1 = 1\<^sub>1 \<cdot>\<^sub>0 1\<^sub>0"
    by simp
  also have "\<dots> = (1\<^sub>1 \<cdot>\<^sub>1 1\<^sub>1) \<cdot>\<^sub>0 (1\<^sub>0 \<cdot>\<^sub>1 1\<^sub>1)"
    by simp
  also have "\<dots> \<le> (1\<^sub>1 \<cdot>\<^sub>0 1\<^sub>0) \<cdot>\<^sub>1 (1\<^sub>1 \<cdot>\<^sub>0 1\<^sub>1)"
    using local.interchange by presburger
  also have "\<dots> = 1\<^sub>1 \<cdot>\<^sub>1 (1\<^sub>1 \<cdot>\<^sub>0 1\<^sub>1)"
    by simp
  also have "\<dots> = 1\<^sub>1 \<cdot>\<^sub>0 1\<^sub>1"
    by simp
  finally have "1\<^sub>1 \<le> 1\<^sub>1 \<cdot>\<^sub>0 1\<^sub>1".
  thus ?thesis
    by (simp add: local.antisym_conv local.id1_comp0)
qed

lemma (in globular_2_semiring) id0_le_id1: "1\<^sub>0 \<le> 1\<^sub>1"
proof-
  have "1\<^sub>0 = 1\<^sub>0 \<cdot>\<^sub>0 1\<^sub>0"
    by simp
  also have "... = (1\<^sub>1 \<cdot>\<^sub>1 1\<^sub>0) \<cdot>\<^sub>0 (1\<^sub>0 \<cdot>\<^sub>1 1\<^sub>1)"
    by simp
  also have "... \<le> (1\<^sub>1 \<cdot>\<^sub>0 1\<^sub>0) \<cdot>\<^sub>1 (1\<^sub>0 \<cdot>\<^sub>0 1\<^sub>1)"
    using local.interchange by blast
  also have "... = 1\<^sub>1 \<cdot>\<^sub>1 1\<^sub>1"
    by simp
  also have "... = 1\<^sub>1"
    by simp
  finally show ?thesis.
qed

lemma (in globular_2_semiring) id0_comp1_eq [simp]: "1\<^sub>0 \<cdot>\<^sub>1 1\<^sub>0 = 1\<^sub>0"
proof-
  have "1\<^sub>0 \<cdot>\<^sub>1 1\<^sub>0 = dom\<^sub>0 1\<^sub>0 \<cdot>\<^sub>1 dom\<^sub>0 1\<^sub>0"
    by simp
  also have "\<dots> = dom\<^sub>1 (dom\<^sub>0 1\<^sub>0) \<cdot>\<^sub>1 dom\<^sub>0 1\<^sub>0"
    using local.d1d0 by presburger
  also have "\<dots> = dom\<^sub>0 1\<^sub>0"
    by simp
  finally show ?thesis
    by simp
qed

lemma (in globular_2_semiring) "1\<^sub>0 = 1\<^sub>1"
  nitpick (* 3-element counterexample *)
  oops

lemma (in globular_2_semiring) d1_id0 [simp]: "dom\<^sub>1 1\<^sub>0 = 1\<^sub>0"
proof-
  have "dom\<^sub>1 1\<^sub>0 = dom\<^sub>1 (dom\<^sub>0 1\<^sub>0)"
    by simp
  also have "\<dots> = dom\<^sub>0 1\<^sub>0"
    using local.d1d0 by blast
  also have "\<dots> = 1\<^sub>0"
    by simp
  finally show ?thesis.
qed

lemma (in globular_2_semiring) d0_id1 [simp]: "dom\<^sub>0 1\<^sub>1 = 1\<^sub>0"
proof-
  have a: "dom\<^sub>0 1\<^sub>1 \<le> 1\<^sub>0"
    by (simp add: local.d0_subid)
  have "1\<^sub>0 \<le> 1\<^sub>1"
    by (simp add: local.id0_le_id1)
  hence "1\<^sub>0 \<le> dom\<^sub>0 1\<^sub>1"
    using local.dsr0.d_iso by fastforce
  thus ?thesis
    using a by auto
qed

lemma (in globular_2_semiring) c0_id1: "cod\<^sub>0 1\<^sub>1 = 1\<^sub>0"
  by simp

lemma (in globular_2_semiring) c0_id0: "cod\<^sub>1 1\<^sub>0 = 1\<^sub>0"
  by simp

lemma (in globular_2_semiring) comm_d0d1: "dom\<^sub>0 (dom\<^sub>1 x) = dom\<^sub>1 (dom\<^sub>0 x)"
proof-
  have "dom\<^sub>0 (dom\<^sub>1 x) = dom\<^sub>0 (dom\<^sub>1 (dom\<^sub>0 x \<cdot>\<^sub>0 x))"
    by simp
  also have "\<dots> = dom\<^sub>0 (dom\<^sub>1 (dom\<^sub>0 x) \<cdot>\<^sub>0 dom\<^sub>1 x)"
    using local.tgsdual.c1_hom by presburger
  also have "\<dots> = dom\<^sub>0 (dom\<^sub>0 x \<cdot>\<^sub>0 dom\<^sub>1 x)"
    by simp
  also have "\<dots> = dom\<^sub>0 x \<cdot>\<^sub>0 dom\<^sub>0 (dom\<^sub>1 x)"
    by simp
  also have "\<dots> = dom\<^sub>1 (dom\<^sub>0 x) \<cdot>\<^sub>0 dom\<^sub>0 (dom\<^sub>1 x)"
    by simp
  also have "\<dots> \<le> dom\<^sub>1 (dom\<^sub>0 x) \<cdot>\<^sub>0 1\<^sub>0"
    using d0.mult_isol local.d0_subid by blast
  finally have a: "dom\<^sub>0 (dom\<^sub>1 x) \<le> dom\<^sub>1 (dom\<^sub>0 x)"
    by simp
  have "dom\<^sub>1 (dom\<^sub>0 x) = dom\<^sub>0 x"
    by simp
  also have "\<dots> = dom\<^sub>0 (dom\<^sub>1 x \<cdot>\<^sub>1 x)"
    by simp
  also have "\<dots> \<le> dom\<^sub>0 (dom\<^sub>1 x) \<cdot>\<^sub>1 dom\<^sub>0 x" 
    using local.d0_weak_hom by blast
  also have "\<dots> \<le> dom\<^sub>0 (dom\<^sub>1 x) \<cdot>\<^sub>1 1\<^sub>0"
    by (simp add: d1.mult_isol local.d0_subid)
  also have "\<dots> \<le> dom\<^sub>0 (dom\<^sub>1 x) \<cdot>\<^sub>1 1\<^sub>1"
    using d1.mult_isol local.id0_le_id1 by presburger
  finally have "dom\<^sub>1 (dom\<^sub>0 x) \<le> dom\<^sub>0 (dom\<^sub>1 x)"
    by simp
  thus ?thesis
    using a by auto
qed

lemma (in globular_2_semiring) comm_d0c1: "dom\<^sub>0 (cod\<^sub>1 x) = cod\<^sub>1 (dom\<^sub>0 x)"
proof-
 have "dom\<^sub>0 (cod\<^sub>1 x) = dom\<^sub>0 (cod\<^sub>1 (dom\<^sub>0 x \<cdot>\<^sub>0 x))"
    by simp
  also have "\<dots> = dom\<^sub>0 (cod\<^sub>1 (dom\<^sub>0 x) \<cdot>\<^sub>0 cod\<^sub>1 x)"
    using local.c1_hom by presburger
  also have "\<dots> = dom\<^sub>0 (dom\<^sub>0 x \<cdot>\<^sub>0 cod\<^sub>1 x)"
    by simp
  also have "\<dots> = dom\<^sub>0 x \<cdot>\<^sub>0 dom\<^sub>0 (cod\<^sub>1 x)"
    by simp
  also have "\<dots> = cod\<^sub>1 (dom\<^sub>0 x) \<cdot>\<^sub>0 dom\<^sub>0 (cod\<^sub>1 x)"
    by simp
  also have "\<dots> \<le> cod\<^sub>1 (dom\<^sub>0 x) \<cdot>\<^sub>0 1\<^sub>0"
    using d0.mult_isol local.d0_subid by blast
  finally have a: "dom\<^sub>0 (cod\<^sub>1 x) \<le> cod\<^sub>1 (dom\<^sub>0 x)"
    by simp
  have "cod\<^sub>1 (dom\<^sub>0 x) = dom\<^sub>0 x"
    by simp
  also have "\<dots> = dom\<^sub>0 (x \<cdot>\<^sub>1 cod\<^sub>1 x)"
    by simp
  also have "\<dots> \<le> dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 (cod\<^sub>1 x)"
    using local.d0_weak_hom by blast
  also have  "\<dots> \<le> 1\<^sub>0 \<cdot>\<^sub>1 dom\<^sub>0 (cod\<^sub>1 x)"
    by (simp add: d1.mult_isor local.d0_subid)
  also have  "\<dots> \<le> 1\<^sub>1 \<cdot>\<^sub>1 dom\<^sub>0 (cod\<^sub>1 x)"
    using d1.mult_isor local.id0_le_id1 by blast
  finally have "cod\<^sub>1 (dom\<^sub>0 x) \<le> dom\<^sub>0 (cod\<^sub>1 x)"
    by simp
  thus ?thesis
    using a by auto
qed

lemma (in globular_2_semiring) comm_c0c1: "cod\<^sub>0 (cod\<^sub>1 x) = cod\<^sub>1 (cod\<^sub>0 x)"
  by (simp add: local.tgsdual.comm_d0d1)

lemma (in globular_2_semiring) comm_c0d1: "cod\<^sub>0 (dom\<^sub>1 x) = dom\<^sub>1 (cod\<^sub>0 x)"
  by (simp add: local.tgsdual.comm_d0c1)

text \<open>We prove further lemmas that are not related to the globular structure.\<close>

lemma (in globular_2_semiring) d0_comp1_idem [simp]: "dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 x = dom\<^sub>0 x"
proof-
  have "dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 x = dom\<^sub>1 (dom\<^sub>0 x) \<cdot>\<^sub>1 dom\<^sub>1 (dom\<^sub>0 x)"
    by simp
  also have "\<dots> =  dom\<^sub>1 (dom\<^sub>0 x)"
    using local.dsr1.d_idem by blast
  also have "\<dots> =  dom\<^sub>0 x"
    by simp
  finally show ?thesis.
qed

lemma (in globular_2_semiring) cod0_comp1_idem: "cod\<^sub>0 x \<cdot>\<^sub>1 cod\<^sub>0 x = cod\<^sub>0 x"
  by simp

lemma (in globular_2_semiring) dom01_loc [simp]: " dom\<^sub>0 (x \<cdot>\<^sub>1 dom\<^sub>1 y) = dom\<^sub>0 (x \<cdot>\<^sub>1 y)"
proof-
  have "dom\<^sub>0 (x \<cdot>\<^sub>1 y) = dom\<^sub>0 (dom\<^sub>1 (x \<cdot>\<^sub>1 y))"
    by (simp add: local.comm_d0d1)
  also have "\<dots> = dom\<^sub>0 (dom\<^sub>1 (x \<cdot>\<^sub>1 dom\<^sub>1 y))"
    by simp
  also have "\<dots> = dom\<^sub>0 (x \<cdot>\<^sub>1 dom\<^sub>1 y)"
    using local.comm_d0d1 local.d1d0 by presburger
  finally show ?thesis..
qed

lemma (in globular_2_semiring) cod01_locl: " cod\<^sub>0 (cod\<^sub>1 x \<cdot>\<^sub>1 y) = cod\<^sub>0 (x \<cdot>\<^sub>1 y)"
  using local.tgsdual.dom01_loc by blast

lemma (in globular_2_semiring) dom01_exp [simp]: "dom\<^sub>0 (cod\<^sub>1 x \<cdot>\<^sub>1 y) = dom\<^sub>0 (x \<cdot>\<^sub>1 y)"
  by (metis local.c1d0 local.cod1_local local.comm_d0c1)

lemma (in globular_2_semiring) cod01_exo: " cod\<^sub>0 (x \<cdot>\<^sub>1 dom\<^sub>1 y) = cod\<^sub>0 (x \<cdot>\<^sub>1 y)"
  using local.tgsdual.dom01_exp by auto  

lemma (in globular_2_semiring) dom01_loc_var [simp]: " dom\<^sub>0 (x \<cdot>\<^sub>0 dom\<^sub>1 y) = dom\<^sub>0 (x \<cdot>\<^sub>0 y)"
proof-
  have "dom\<^sub>0 (x \<cdot>\<^sub>0 y) = dom\<^sub>0 (x \<cdot>\<^sub>0 dom\<^sub>0 y)"
    by simp
  also have "\<dots> = dom\<^sub>0 (x \<cdot>\<^sub>0 dom\<^sub>1 (dom\<^sub>0 y))"
    by simp
  also have "\<dots> = dom\<^sub>0 (x \<cdot>\<^sub>0 dom\<^sub>0 (dom\<^sub>1 y))"
    by (simp add: local.comm_d0d1)
  also have "\<dots> = dom\<^sub>0 (x \<cdot>\<^sub>0 dom\<^sub>1 y)"
    by simp
    finally show ?thesis..
  qed

lemma (in globular_2_semiring) cod01_loc_var: " cod\<^sub>0 (cod\<^sub>1 x \<cdot>\<^sub>0 y) = cod\<^sub>0 (x \<cdot>\<^sub>0 y)"
  using local.tgsdual.dom01_loc by fastforce

lemma (in globular_2_semiring) dom0cod1_exp: " dom\<^sub>0 (cod\<^sub>1 x \<cdot>\<^sub>0 y) = dom\<^sub>0 (x \<cdot>\<^sub>0 y)"
  by (metis local.c1d0 local.comm_d0c1 local.d0_local local.tgsdual.d1_hom)

lemma (in globular_2_semiring) cod0dom1_exp: "cod\<^sub>0 (x \<cdot>\<^sub>0 dom\<^sub>1 y) = cod\<^sub>0 (x \<cdot>\<^sub>0 y)"
  using local.tgsdual.dom0cod1_exp by blast

lemma (in globular_2_semiring) d0_comp1: "dom\<^sub>0 x \<cdot>\<^sub>0 (y \<cdot>\<^sub>1 z) \<le> (dom\<^sub>0 x \<cdot>\<^sub>0 y) \<cdot>\<^sub>1 (dom\<^sub>0 x \<cdot>\<^sub>0 z)"
proof-
  have "dom\<^sub>0 x \<cdot>\<^sub>0 (y \<cdot>\<^sub>1 z) = (dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 x) \<cdot>\<^sub>0 (y \<cdot>\<^sub>1 z)"
    by simp
  also have "\<dots> \<le> (dom\<^sub>0 x \<cdot>\<^sub>0 y) \<cdot>\<^sub>1 (dom\<^sub>0 x \<cdot>\<^sub>0 z)"
    using local.interchange by presburger
  finally show ?thesis.
qed

lemma (in globular_2_semiring) d1_comp1: "dom\<^sub>1 x \<cdot>\<^sub>0 (y \<cdot>\<^sub>1 z) \<le> (dom\<^sub>1 x \<cdot>\<^sub>0 y) \<cdot>\<^sub>1 (dom\<^sub>1 x \<cdot>\<^sub>0 z)"
  by (metis local.dsr1.d_idem local.tgsdual.interchange)

lemma (in globular_2_semiring) d01_export: "dom\<^sub>0 (dom\<^sub>1 x \<cdot>\<^sub>1 y) \<le> dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 y"
proof-
  have "dom\<^sub>0 (dom\<^sub>1 x \<cdot>\<^sub>1 y) \<le> dom\<^sub>0 (dom\<^sub>1 x) \<cdot>\<^sub>1 dom\<^sub>0 y"
    by (simp add: local.d0_weak_hom)
  also have "\<dots> = dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 y"
    by (simp add: local.comm_d0d1)
  finally show ?thesis.
qed

lemma (in globular_2_semiring) cod01_export: "cod\<^sub>0 (x \<cdot>\<^sub>1 cod\<^sub>1 y) \<le> cod\<^sub>0 x \<cdot>\<^sub>1 cod\<^sub>0 y"
  by (simp add: local.tgsdual.d01_export)

lemma (in globular_2_semiring) d10_export [simp]: "dom\<^sub>1 (dom\<^sub>0 x \<cdot>\<^sub>1 y) = dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>1 y"
  by (metis local.d1d0 local.dsr1.d_export)

lemma (in globular_2_semiring) cod10_export: "cod\<^sub>1 (x \<cdot>\<^sub>1 cod\<^sub>0 y) = cod\<^sub>1 x \<cdot>\<^sub>1 cod\<^sub>0 y"
  by simp

lemma (in globular_2_semiring) d0_comp10: "dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 y = dom\<^sub>0 x \<cdot>\<^sub>0 dom\<^sub>0 y"
proof (rule order.antisym)
  have "dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 y \<le> dom\<^sub>0 (dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 y) \<cdot>\<^sub>0 (dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 y)"
    by simp
  also have "\<dots> \<le> (dom\<^sub>0 (dom\<^sub>0 x) \<cdot>\<^sub>1 dom\<^sub>0 (dom\<^sub>0 y)) \<cdot>\<^sub>0 (dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 y)"
    using d0.mult_isor local.tgsdual.c0_weak_hom by blast
  also have "\<dots> \<le> (dom\<^sub>0 x \<cdot>\<^sub>1 1\<^sub>0) \<cdot>\<^sub>0 (1\<^sub>0 \<cdot>\<^sub>1 dom\<^sub>0 y)"
    by (simp add: d0.mult_iso d1.mult_isol d1.mult_isor local.d0_subid)
  also have "\<dots> \<le> (dom\<^sub>0 x \<cdot>\<^sub>1 1\<^sub>1) \<cdot>\<^sub>0 (1\<^sub>1 \<cdot>\<^sub>1 dom\<^sub>0 y)"
    using d1.mult_isol d1.mult_isor local.d0.dd.mult_iso local.id0_le_id1 by presburger
  also have "\<dots> \<le> dom\<^sub>0 x \<cdot>\<^sub>0 dom\<^sub>0 y"
    by simp
  finally show "dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 y \<le> dom\<^sub>0 x \<cdot>\<^sub>0 dom\<^sub>0 y".
next
  have "dom\<^sub>0 x \<cdot>\<^sub>0 dom\<^sub>0 y = (dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 x) \<cdot>\<^sub>0 (dom\<^sub>0 y \<cdot>\<^sub>1 dom\<^sub>0 y)"
    by simp
  also have "\<dots> \<le> (dom\<^sub>0 x \<cdot>\<^sub>0 dom\<^sub>0 y) \<cdot>\<^sub>1 (dom\<^sub>0 x \<cdot>\<^sub>0 dom\<^sub>0 y)"
    using local.interchange by blast
  also have "\<dots> \<le> (dom\<^sub>0 x \<cdot>\<^sub>0 1\<^sub>0) \<cdot>\<^sub>1 (1\<^sub>0 \<cdot>\<^sub>0 dom\<^sub>0 y)"
    by (metis d0.mult_isol local.d0_subid local.d0_id1 local.d1.dd.mult_iso local.dsr0.d_comm)
  also have "\<dots> = dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 y"
    by simp
  finally show "dom\<^sub>0 x \<cdot>\<^sub>0 dom\<^sub>0 y \<le> dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 y".
qed

lemma (in globular_2_semiring) dom_exchange_strong: "(dom\<^sub>0 w \<cdot>\<^sub>1 dom\<^sub>0 x) \<cdot>\<^sub>0 (dom\<^sub>0 y \<cdot>\<^sub>1 dom\<^sub>0 z) = (dom\<^sub>0 w \<cdot>\<^sub>0 dom\<^sub>0 y) \<cdot>\<^sub>1 (dom\<^sub>0 x \<cdot>\<^sub>0 dom\<^sub>0 z)"
proof-
  have  "(dom\<^sub>0 w \<cdot>\<^sub>1 dom\<^sub>0 x) \<cdot>\<^sub>0 (dom\<^sub>0 y \<cdot>\<^sub>1 dom\<^sub>0 z) = (dom\<^sub>0 w \<cdot>\<^sub>0 dom\<^sub>0 x) \<cdot>\<^sub>0 (dom\<^sub>0 y \<cdot>\<^sub>0 dom\<^sub>0 z)"
    by (simp add: local.d0_comp10)
  also have "\<dots> = (dom\<^sub>0 w \<cdot>\<^sub>0 dom\<^sub>0 y) \<cdot>\<^sub>0 (dom\<^sub>0 x \<cdot>\<^sub>0 dom\<^sub>0 z)"
    by (metis local.d0.dd.mult_assoc local.dsr0.d_comm)
  also have  "\<dots> = dom\<^sub>0 (dom\<^sub>0 w \<cdot>\<^sub>0 dom\<^sub>0 y) \<cdot>\<^sub>0 dom\<^sub>0 (dom\<^sub>0 x \<cdot>\<^sub>0 dom\<^sub>0 z)"
    by simp
  also have  "\<dots> = dom\<^sub>0 (dom\<^sub>0 w \<cdot>\<^sub>0 dom\<^sub>0 y) \<cdot>\<^sub>1 dom\<^sub>0 (dom\<^sub>0 x \<cdot>\<^sub>0 dom\<^sub>0 z)"
    using local.d0_comp10 by presburger
  also have  "\<dots> = (dom\<^sub>0 w \<cdot>\<^sub>0 dom\<^sub>0 y) \<cdot>\<^sub>1 (dom\<^sub>0 x \<cdot>\<^sub>0 dom\<^sub>0 z)"
    by simp
  finally show ?thesis.
qed

text \<open>The following laws are diamond laws. It remains to define diamonds for them.\<close>

lemma (in globular_2_semiring) fdia0fdia1_prop: "dom\<^sub>0 (y \<cdot>\<^sub>0 dom\<^sub>1 (x \<cdot>\<^sub>1 z)) = dom\<^sub>0 (y \<cdot>\<^sub>0 (x \<cdot>\<^sub>1 z))"
  by simp

lemma (in globular_2_semiring) bdia0fdia1_prop [simp]: "cod\<^sub>0 (dom\<^sub>1 (x \<cdot>\<^sub>1 z) \<cdot>\<^sub>0 y) = cod\<^sub>0 ((x \<cdot>\<^sub>1 z) \<cdot>\<^sub>0 y)"
  by (metis local.comm_c0d1 local.d1_hom local.d1c0 local.dsr1.d_invol)

lemma (in globular_2_semiring) fdia0bdia1_prop: "dom\<^sub>0 (y \<cdot>\<^sub>0 cod\<^sub>1 (x \<cdot>\<^sub>1 z)) = dom\<^sub>0 (y \<cdot>\<^sub>0 (x \<cdot>\<^sub>1 z))"
  by simp

lemma (in globular_2_semiring) bdia0bdia1_prop: "cod\<^sub>0 (cod\<^sub>1 (x \<cdot>\<^sub>1 z) \<cdot>\<^sub>0 y) = cod\<^sub>0 ((x \<cdot>\<^sub>1 z) \<cdot>\<^sub>0 y)"
  by simp

lemma (in globular_2_semiring) fdia0fdia1_prop2: "dom\<^sub>0 (y \<cdot>\<^sub>0 dom\<^sub>1 (x \<cdot>\<^sub>1 z)) \<le> dom\<^sub>0 (y \<cdot>\<^sub>0 (dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 z))"
proof-
  have "dom\<^sub>0 (y \<cdot>\<^sub>0 dom\<^sub>1 (x \<cdot>\<^sub>1 z)) = dom\<^sub>0 (y \<cdot>\<^sub>0 dom\<^sub>0 (x \<cdot>\<^sub>1 z))"
    by simp
  also have "\<dots> \<le> dom\<^sub>0 (y \<cdot>\<^sub>0 (dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 z))"
    using d0.mult_isol local.dsr0.d_iso local.tgsdual.c0_weak_hom by presburger
  finally show ?thesis.
qed

lemma (in globular_2_semiring) fdia00_prop2: "dom\<^sub>0 (y \<cdot>\<^sub>0 dom\<^sub>0 (x \<cdot>\<^sub>1 z)) \<le> dom\<^sub>0 (y \<cdot>\<^sub>0 (dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 z))"
  using local.fdia0fdia1_prop2 by auto
 
lemma (in globular_2_semiring) bdia0dom1_prop2: "cod\<^sub>0 (dom\<^sub>1 (x \<cdot>\<^sub>1 z) \<cdot>\<^sub>0 y) \<le> cod\<^sub>0 ((cod\<^sub>0 x \<cdot>\<^sub>1 cod\<^sub>0 z) \<cdot>\<^sub>0 y)"
  using local.tgsdual.fdia00_prop2 by auto

lemma (in globular_2_semiring) bdia0dom0_prop2: "cod\<^sub>0 (dom\<^sub>0 (x \<cdot>\<^sub>1 z) \<cdot>\<^sub>0 y) \<le> cod\<^sub>0 ((dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 z) \<cdot>\<^sub>0 y)"
  by (simp add: d0.mult_isor local.csr0.coddual.d_iso local.tgsdual.c0_weak_hom)

lemma (in globular_2_semiring) fdia0bdia1_prop_2: "dom\<^sub>0 (y \<cdot>\<^sub>0 cod\<^sub>1 (z \<cdot>\<^sub>1 x)) \<le> dom\<^sub>0 (y \<cdot>\<^sub>0 (dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 z))"
  by (metis local.d0_comp10 local.dsr0.d_comm local.tgsdual.bdia0dom1_prop2)

lemma (in globular_2_semiring) fdia0bdiao_prop2: "dom\<^sub>0 (y \<cdot>\<^sub>0 cod\<^sub>0 (z \<cdot>\<^sub>1 x)) \<le> dom\<^sub>0 (y \<cdot>\<^sub>0 (cod\<^sub>0 z \<cdot>\<^sub>1 cod\<^sub>0 x))"
  by (simp add: local.tgsdual.bdia0dom0_prop2)

lemma (in globular_2_semiring) bdia0bdia1_prop2: "cod\<^sub>0 (cod\<^sub>1 (z \<cdot>\<^sub>1 x) \<cdot>\<^sub>0 y) \<le> cod\<^sub>0 ((cod\<^sub>0 x \<cdot>\<^sub>1 cod\<^sub>0 z) \<cdot>\<^sub>0 y)"
  using local.tgsdual.fdia0bdia1_prop_2 by auto

lemma (in globular_2_semiring) bdia0bdia0_prop2: "cod\<^sub>0 (cod\<^sub>0 (x \<cdot>\<^sub>1 z) \<cdot>\<^sub>0 y) \<le> cod\<^sub>0 ((cod\<^sub>0 x \<cdot>\<^sub>1 cod\<^sub>0 z) \<cdot>\<^sub>0 y)"
  using local.tgsdual.fdia00_prop2 by auto
 
lemma (in globular_2_semiring) fdia1fdia0_prop3 [simp]: "dom\<^sub>1 (x \<cdot>\<^sub>1 dom\<^sub>0 (dom\<^sub>1 y \<cdot>\<^sub>0 z)) = dom\<^sub>1 (x \<cdot>\<^sub>1 dom\<^sub>0 (y \<cdot>\<^sub>0 z))"
  by (metis local.comm_d0d1 local.d1_hom local.d1d0 local.dom01_loc_var)

lemma (in globular_2_semiring) fdia1bdia0_prop3 [simp]: "dom\<^sub>1 (x \<cdot>\<^sub>1 cod\<^sub>0 (z \<cdot>\<^sub>0 dom\<^sub>1 y)) = dom\<^sub>1 (x \<cdot>\<^sub>1 cod\<^sub>0 (z \<cdot>\<^sub>0 y))"
  by (simp add: local.tgsdual.dom0cod1_exp)

lemma (in globular_2_semiring) bdia1fdia0_prop3: "cod\<^sub>1 (dom\<^sub>0 (cod\<^sub>1 y \<cdot>\<^sub>0 z) \<cdot>\<^sub>1 x) = cod\<^sub>1 (dom\<^sub>0 (y \<cdot>\<^sub>0 z) \<cdot>\<^sub>1 x)"
  by simp

lemma (in globular_2_semiring) bdia1bdia0_prop3: " cod\<^sub>1 (cod\<^sub>0 (z \<cdot>\<^sub>0 cod\<^sub>1 y) \<cdot>\<^sub>1 x) = cod\<^sub>1 (cod\<^sub>0 (z \<cdot>\<^sub>0 y) \<cdot>\<^sub>1 x)"
  by simp

lemma (in globular_2_semiring) fdia0fdia1_prop4: "dom\<^sub>0 z \<cdot>\<^sub>0 dom\<^sub>1 (x \<cdot>\<^sub>1 y) \<le> dom\<^sub>1 ((dom\<^sub>0 z \<cdot>\<^sub>0 x) \<cdot>\<^sub>1 (dom\<^sub>0 z \<cdot>\<^sub>0 y))"
proof-
  have  "dom\<^sub>0 z \<cdot>\<^sub>0 dom\<^sub>1 (x \<cdot>\<^sub>1 y) = dom\<^sub>1 (dom\<^sub>0 z) \<cdot>\<^sub>0 dom\<^sub>1 (x \<cdot>\<^sub>1 y)"
    by simp
  also have "\<dots> = dom\<^sub>1 (dom\<^sub>0 z \<cdot>\<^sub>0 (x \<cdot>\<^sub>1 y))"
    by simp
  also have "\<dots> \<le> dom\<^sub>1 ((dom\<^sub>0 z \<cdot>\<^sub>0 x) \<cdot>\<^sub>1 (dom\<^sub>0 z  \<cdot>\<^sub>0 y))"
    using local.d0_comp1 local.dsr1.d_iso by presburger
  finally show ?thesis.
qed

lemma (in globular_2_semiring) fdia0bdia1_prop4: "dom\<^sub>0 z \<cdot>\<^sub>0 cod\<^sub>1 (y \<cdot>\<^sub>1 x) \<le> cod\<^sub>1 ((dom\<^sub>0 z \<cdot>\<^sub>0 y) \<cdot>\<^sub>1 (dom\<^sub>0 z \<cdot>\<^sub>0 x))"
  by (metis local.c1d0 local.csr1.coddual.d_iso local.d0_comp1 local.tgsdual.d1_hom)

lemma (in globular_2_semiring) fdia1fdia1_prop4:  "dom\<^sub>1 (x \<cdot>\<^sub>1 y) \<cdot>\<^sub>0 dom\<^sub>0 z \<le> dom\<^sub>1 ((x \<cdot>\<^sub>0 dom\<^sub>0 z) \<cdot>\<^sub>1 (y \<cdot>\<^sub>0 dom\<^sub>0 z))"
  by (metis local.cd_compat0 local.tgsdual.fdia0bdia1_prop4)

lemma (in globular_2_semiring) bdia1bdia1_prop4:  "cod\<^sub>1 (y \<cdot>\<^sub>1 x) \<cdot>\<^sub>0 dom\<^sub>0 z \<le> cod\<^sub>1 ((y \<cdot>\<^sub>0 dom\<^sub>0 z) \<cdot>\<^sub>1 (x \<cdot>\<^sub>0 dom\<^sub>0 z))"
  by (metis local.cd_compat0 local.tgsdual.fdia0fdia1_prop4)


subsection \<open>globular 2-Kleene algebras\<close>

class globular_2_kleene_algebra = globular_2_semiring + kleene_algebra0 + kleene_algebra1 

lemma (in globular_2_kleene_algebra) "star1 x \<cdot>\<^sub>0 star1 y \<le> star0 (x \<cdot>\<^sub>1 y)"
  nitpick (* 3-element counterexample *)
  oops

lemma (in globular_2_kleene_algebra) "star1 x \<cdot>\<^sub>0 star1 y \<le> star1 (x \<cdot>\<^sub>1 y)"
  nitpick (* 3-element counterexample *)
  oops

lemma (in globular_2_kleene_algebra) interchange_var1: "(x \<cdot>\<^sub>1 x) \<cdot>\<^sub>0 (y \<cdot>\<^sub>1 y) \<cdot>\<^sub>0 (z \<cdot>\<^sub>1 z) \<le> (x \<cdot>\<^sub>0 y \<cdot>\<^sub>0 z) \<cdot>\<^sub>1 (x \<cdot>\<^sub>0 y \<cdot>\<^sub>0 z)"
  by (meson d0.mult_iso local.interchange local.order.refl local.order.trans)

lemma (in globular_2_kleene_algebra) interchange_var2: "(x \<cdot>\<^sub>1 y) \<cdot>\<^sub>0 (x \<cdot>\<^sub>1 y) \<cdot>\<^sub>0 (x \<cdot>\<^sub>1 y) \<le> (x \<cdot>\<^sub>0 x \<cdot>\<^sub>0 x) \<cdot>\<^sub>1 (y \<cdot>\<^sub>0 y \<cdot>\<^sub>0 y)"
  by (meson d0.mult_iso local.interchange local.order.refl local.order.trans)

lemma (in globular_2_kleene_algebra) " star1 (x \<cdot>\<^sub>1 y) \<le> star1 x \<cdot>\<^sub>0 star1 y"
  nitpick (* 6-element counterexample *)
  oops

lemma (in globular_2_kleene_algebra) "star1 x \<cdot>\<^sub>0 star1 y \<le> star1 (x \<cdot>\<^sub>0 y)"
  nitpick (* 3-element counterexample *)
  oops

lemma (in globular_2_kleene_algebra) "star1 (x \<cdot>\<^sub>0 y) \<le> star1 x \<cdot>\<^sub>0 star1 y"
  nitpick (* 6-element counterexample *)
  oops

lemma (in globular_2_kleene_algebra) "star0 x \<cdot>\<^sub>1 star0 y \<le> star0 (x \<cdot>\<^sub>0 y)"
  nitpick (* 3-element counterexample *)
  oops

lemma (in globular_2_kleene_algebra) " star0 (x \<cdot>\<^sub>0 y) \<le> star0 x \<cdot>\<^sub>1 star0 y"
  nitpick (* 3-element counterexample *)
  oops

lemma (in globular_2_kleene_algebra) "star0 x \<cdot>\<^sub>1 star0 y \<le> star0 (x \<cdot>\<^sub>1 y)"
  nitpick (* 3-element counterexample *)
  oops

lemma (in globular_2_kleene_algebra) star0_comp1: "star0 (x \<cdot>\<^sub>1 y) \<le> star0 x \<cdot>\<^sub>1 star0 y"
proof-
  have a: "1\<^sub>0 \<le> star0 x \<cdot>\<^sub>1 star0 y"
    by (metis k0.one_le_star local.d1.dd.mult_iso local.id0_comp1_eq)
  have "(x \<cdot>\<^sub>1 y) \<cdot>\<^sub>0 (star0 x \<cdot>\<^sub>1 star0 y) \<le> (x \<cdot>\<^sub>0 star0 x ) \<cdot>\<^sub>1 (y \<cdot>\<^sub>0 star0 y)"
    by (simp add: local.interchange)
  also have "\<dots> \<le> star0 x \<cdot>\<^sub>1 star0 y"
    by (simp add: k0.star_unfoldlr local.d1.dd.mult_iso)
  finally have "(x \<cdot>\<^sub>1 y) \<cdot>\<^sub>0 (star0 x \<cdot>\<^sub>1 star0 y) \<le> star0 x \<cdot>\<^sub>1 star0 y".
  hence "1\<^sub>0 + (x \<cdot>\<^sub>1 y) \<cdot>\<^sub>0 (star0 x \<cdot>\<^sub>1 star0 y) \<le> star0 x \<cdot>\<^sub>1 star0 y"
    using a local.add_lub by force
  thus ?thesis
    using local.star0_inductl by force
qed

lemma (in globular_2_kleene_algebra) "dom\<^sub>0 x \<cdot>\<^sub>0 star1 y \<le> star1 (dom\<^sub>0 x \<cdot>\<^sub>0 y)" 
  oops (* no proof no counterexample *)
 
text \<open>We need to add the star axioms we want for rewriting.\<close>


end