MyCharacter := function(S, D, h, k)
  local H, map, HH, e, mults, lvals, l, lp, x, pos, total, r, rp, i;

  H   := GroupHClass(D);
  map := IsomorphismPermGroup(H);
  HH  := Range(map);
  e   := MultiplicativeNeutralElement(H);
  if H = fail then
    Error();
  elif not e in H then
    Error();
  fi;
  mults := LambdaOrbMults(LambdaOrb(D), LambdaOrbSCCIndex(D));
  lvals := ListWithIdenticalEntries(Length(ConjugacyClasses(HH)), 0);

  for i in LambdaOrbSCC(D) do
    l  := mults[i][1];
    lp := mults[i][2];
    x  := e * l * k * lp;
    if x in H then
      pos := Position(ConjugacyClasses(HH), ConjugacyClass(HH, x ^ map));
      lvals[pos] := lvals[pos] + 1;
    fi;
  od;

  total := 0;
  mults := RhoOrbMults(RhoOrb(D), RhoOrbSCCIndex(D));
  for i in RhoOrbSCC(D) do
    r  := mults[i][1];
    rp := mults[i][2];
    x  := rp * h * r * e;
    if x in H then
      pos := Position(ConjugacyClasses(HH), ConjugacyClass(HH, x ^ map));

      total := total + lvals[pos] * Size(Centraliser(HH, x ^ map));
    fi;
  od;
  return total;
end;

# MyCharacter := function(S, h, k)
#   local deg, lfilt, rfilt, L, R, H, n, d, r, l, x;
# 
#   deg := DegreeOfTransformationSemigroup(S);
# 
#   lfilt := function(l)
#     return Representative(l) * k in l;
#   end;
# 
#   rfilt := function(r)
#     return h * Representative(r) in r;
#   end;
#   for d in DClasses(S) do 
#     L := Filtered(LClasses(d), lfilt);
#     R := Filtered(RClasses(d), rfilt);
#     H := [];
#     for r in R do
#       Append(H, Filtered(HClasses(r), lfilt));
#     od;
#     for l in L do
#       Append(H, Filtered(HClasses(l), rfilt));
#     od;
#     for x in H do
#       n :=  Number(x, s -> h * s * k = s);
#       if n<> 0 and Size(x) mod n <> 0 then
#         Error("here");
#       fi;
#     od;
#   od;
# #     if IsGroupHClass(x) then 
# #       map := IsomorphismPermGroup(x);
# #       e := Idempotents(x)[1];
# #       Print("##########################################\n");
# #       Print("h:= ", h, "\nk:= ", k, "\ne :=", e, "\n");
# #       Print("Actual number is: ", Number(x, s -> h * s * k = s), "\n");
# #       Print("Size of centraliser is: ", Size(Centraliser(Range(map), (e * h *
# #       e) ^ map)), "\n");
# #       Print("ehe and eke are in the same conjugacy class: ", 
# #       (e * h * e) ^ map in ConjugacyClass(Range(map), (e * k * e) ^ map),
# #       "\n");
# #     fi;
#   # return Size(Set(out));
#   return 0;
# end;

ConjugacyClassReps := function(S)
  local D, out, C, map;
  
  D := List(RegularDClasses(S), GroupHClass);
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
