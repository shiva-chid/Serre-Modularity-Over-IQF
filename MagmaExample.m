// Learn about these intrinsics, specifically HeckeCharacterGroup which I didn't go over today
// It is the dual of RayClassGroup

RayClassGroup;
?RayClassGroup

RayClassField;

HeckeCharacterGroup;

/////////////////////////////////////////////////////////////////////

// Example 1
// Abelian extensions of Q
K := RationalsAsNumberField();
OK := RingOfIntegers(K);
I := 5*OK;
RayClassGroup(I);
L := NumberField(RayClassField(I)); L; // It is the quadratic field Q(\sqrt{5})

RayClassGroup(I,[1]);
L := NumberField(RayClassField(I,[1])); L; // If we allow the infinite place to be ramified, we get Q(\zeta_5)

I := 13*OK;
RayClassGroup(I);
L := NumberField(RayClassField(I)); L; // It is the totally real sub-field Q(\zeta_13 + \zeta_13^-1) of Q(\zeta_13)

RayClassGroup(I,[1]);
L := NumberField(RayClassField(I,[1])); L; // If we allow the infinite place to be ramified, we get Q(\zeta_13)


// Example 2
// Abelian extensions of Q(\sqrt{-1})
K<i> := QuadraticField(-1);
OK := RingOfIntegers(K);
I := 5*OK;
RayClassGroup(I);
L := NumberField(RayClassField(I)); L;
Labs := AbsoluteField(L); Labs;
IsIsomorphic(Labs,CyclotomicField(20));

