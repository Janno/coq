Test Typeclasses Default Unification Evarconv.
Unset Typeclasses Default Unification Evarconv.
Test Typeclasses Default Unification Evarconv.
Set Typeclasses Default Unification Evarconv.
Test Typeclasses Default Unification Evarconv.

Class EvarconvAboutTest : Prop := {}.

About EvarconvAboutTest.

Unset Typeclasses Default Unification Evarconv.
About EvarconvAboutTest.

Add Typeclass Evarconv EvarconvAboutTest.
About EvarconvAboutTest.

Remove Typeclass Evarconv EvarconvAboutTest.
Set Typeclasses Default Unification Evarconv.
Add Typeclass Legacy EvarconvAboutTest.
About EvarconvAboutTest.

Add Typeclass Evarconv EvarconvAboutTest.
About EvarconvAboutTest.

Remove Typeclass Evarconv EvarconvAboutTest.
Remove Typeclass Legacy EvarconvAboutTest.

Class EvarconvTableTest : Prop := {}.

Add Typeclass Evarconv EvarconvTableTest.
Print Table Typeclass Evarconv.
Remove Typeclass Evarconv EvarconvTableTest.
Print Table Typeclass Evarconv.

Add Typeclass Legacy EvarconvTableTest.
Print Table Typeclass Legacy.
Remove Typeclass Legacy EvarconvTableTest.
Print Table Typeclass Legacy.

Unset Typeclasses Default Unification Evarconv.
Class EvarconvResolutionTest : Prop := {}.
Add Typeclass Evarconv EvarconvResolutionTest.
#[export] Instance evarconv_resolution_test : EvarconvResolutionTest := {}.
Set Typeclasses Debug.
Goal EvarconvResolutionTest.
Proof.
  typeclasses eauto.
Qed.
Unset Typeclasses Debug.
