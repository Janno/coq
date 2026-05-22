Test Typeclasses Default Unification Evarconv.
Unset Typeclasses Default Unification Evarconv.
Test Typeclasses Default Unification Evarconv.
Set Typeclasses Default Unification Evarconv.
Test Typeclasses Default Unification Evarconv.

Class EvarconvTableTest : Prop := {}.

Add Typeclass Evarconv EvarconvTableTest.
Print Table Typeclass Evarconv.
Remove Typeclass Evarconv EvarconvTableTest.
Print Table Typeclass Evarconv.

Add Typeclass Legacy EvarconvTableTest.
Print Table Typeclass Legacy.
Remove Typeclass Legacy EvarconvTableTest.
Print Table Typeclass Legacy.
