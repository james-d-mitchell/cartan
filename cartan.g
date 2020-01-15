MyCharacter := function(S, h, k)
  local deg, lfilt, L, rfilt, R, H, out, map, e, r, l, x;

  deg := DegreeOfTransformationSemigroup(S);

  lfilt := function(l)
    local im;
    im := ImageSetOfTransformation(Representative(l));
    return OnSets(im, k) = im;
  end;
  L := Filtered(LClasses(S), lfilt);

  rfilt := function(r)
    local ker;
    ker := FlatKernelOfTransformation(Representative(r), deg);
    return OnKernelAntiAction(ker, h) = ker;
  end;
  R := Filtered(RClasses(S), rfilt);
  H := [];
  for r in R do
    Append(H, Filtered(HClasses(r), lfilt));
  od;
  for l in L do
    Append(H, Filtered(HClasses(l), rfilt));
  od;
  out := [];
  for x in H do
    Append(out, Filtered(x, s -> h * s * k = s));
    if IsGroupHClass(x) then 
      map := IsomorphismPermGroup(x);
      e := Idempotents(x)[1];
      Print("##########################################\n");
      Print("h:= ", h, "\nk:= ", k, "\ne :=", e, "\n");
      Print("Actual number is: ", Number(x, s -> h * s * k = s), "\n");
      Print("Size of centraliser is: ", Size(Centraliser(Range(map), (e * h *
      e) ^ map)), "\n");
      Print("ehe and eke are in the same conjugacy class: ", 
      (e * h * e) ^ map in ConjugacyClass(Range(map), (e * k * e) ^ map),
      "\n");
    fi;
  od;
  return Size(Set(out));
end;

ConjugacyClassReps := function(S)
  local D, out, C, map;
  
  D := List(DClasses(S), GroupHClass);
  D := List(D, IsomorphismPermGroup);
  out := [];
  for map in D do 
    C := List(ConjugacyClasses(Range(map)), Representative);
    map := InverseGeneralMapping(map);
    C := List(C, x -> x ^ map);
    Append(out, C);
  od;
  return out;
end;

MyCartanMatrix := function(S)
  local C, n, mat, i, j;
  C := ConjugacyClassReps(S);
  n := Length(C);
  mat := List([1 .. n], x -> []);
  for i in [1 .. n] do
    for j in [1 .. n] do 
      mat[i][j] := MyCharacter(S, C[i], C[j]);
    od;
  od;
  return mat;
end;

Bug := function(S, h, k)
  local deg, lfilt, L, rfilt, R, H, out, map, e, r, l, x;

  deg := DegreeOfTransformationSemigroup(S);

  lfilt := function(l)
    local im;
    im := ImageSetOfTransformation(Representative(l));
    return OnSets(im, k) = im;
  end;
  L := Filtered(LClasses(S), lfilt);

  rfilt := function(r)
    local ker;
    ker := FlatKernelOfTransformation(Representative(r), deg);
    return OnKernelAntiAction(ker, h) = ker;
  end;
  R := Filtered(RClasses(S), rfilt);
  H := [];
  for r in R do
    Append(H, Filtered(HClasses(r), lfilt));
  od;
  for l in L do
    Append(H, Filtered(HClasses(l), rfilt));
  od;
  out := [];
  for x in H do
    Append(out, Filtered(x, s -> h * s * k = s));
    if IsGroupHClass(x) then 
      map := IsomorphismPermGroup(x);
      e := Idempotents(x)[1];
      Print("##########################################\n");
      Print("h:= ", h, "\nk:= ", k, "\ne :=", e, "\n");
      Print("Actual number is: ", Number(x, s -> h * s * k = s), "\n");
      Print("Size of centraliser is: ", Size(Centraliser(Range(map), (e * h *
      e) ^ map)), "\n");
      Print("ehe and eke are in the same conjugacy class: ", 
      (e * h * e) ^ map in ConjugacyClass(Range(map), (e * k * e) ^ map),
      "\n");
    fi;
  od;
  return Size(Set(out));
end;
S := FullTransformationMonoid(4);
h := IdentityTransformation;
k := IdentityTransformation;
Bug(S, h, k);
