# Re-flemme

LoadPackage("semigroups");
Read("cartan.g");
Todd := FullTransformationMonoid(4);
DDc := RegularDClasses(Todd)[3];
ee := MultiplicativeNeutralElement(GroupHClass(DDc));

LClassRadical := function(S, e)
  local D, H, ord, map, HH, LHH, deg, invmap,
        im_e, l_e_box, l_mults, l_to_first, l_from_first,
        ker_e, r_e_box, r_mults, r_to_first, r_from_first,
        l_transitions, nb_R_classes, l_returns, r_transitions, nb_L_classes,
        M, Rad, c, j, r, k, i, l, x;

  D   := DClass(S, e);
  H   := HClass(S, e);
  ord := Number(H);
  map := IsomorphismPermGroup(H);
  HH  := Range(map);
  LHH := List(HH);
  #e   := MultiplicativeNeutralElement(H);
  deg := DegreeOfTransformationSemigroup(S);
  invmap := InverseGeneralMapping(map);

  # To go to the L-classes
  im_e    := ImageSetOfTransformation(e, deg);
  l_e_box := Position(LambdaOrb(D), im_e);

  l_mults      := LambdaOrbMults(LambdaOrb(D), LambdaOrbSCCIndex(D));
  l_to_first   := l_mults[l_e_box][2];
  l_from_first := l_mults[l_e_box][1];

  # To go to the R-classes
  ker_e   := FlatKernelOfTransformation(e, deg);
  r_e_box := Position(RhoOrb(D), ker_e);

  r_mults := RhoOrbMults(RhoOrb(D), RhoOrbSCCIndex(D));
  r_to_first   := r_mults[r_e_box][2];
  r_from_first := r_mults[r_e_box][1];

  l_transitions := List(LambdaOrbSCC(D), i -> e * l_to_first * l_mults[i][1]);
  nb_R_classes  := Length(l_transitions);
  l_returns     := List(LambdaOrbSCC(D), i -> l_mults[i][2] * l_from_first);
  r_transitions := List(RhoOrbSCC(D),    i -> r_mults[i][1] * r_to_first * e);
  nb_L_classes  := Length(r_transitions);

  M := List([1 .. ord * nb_L_classes], x -> List([1 .. ord * nb_R_classes], x -> 0));

  c := 0;
  for k in H do
    for i in [1 .. nb_L_classes] do
      r := r_transitions[i];
      for j in [1 .. nb_R_classes] do
        l  := l_transitions[j];
        if (l * r) in H then
          x := (k ^ map) * ((l * r) ^ map) ^ (-1);
          M[i + nb_L_classes * c][(j - 1) * ord + Position(LHH, x)] := 1;
        fi;
      od;
    od;
    c := c + 1;
  od;

  Rad := NullspaceMat(TransposedMatMutable(M));
  #Print(Length(Rad[1]), "\t", Length(Rad));
  #Error();
  return rec( rad := Rad, transitions := l_transitions,
              returns := l_returns, HList := LHH, morph := map);
end;

RadicalBicharacter := function(S, e)
  local Rec, Rad, LHH, map, l_transitions, l_returns,
        ListLClass, n, H, ord, B, dim,
        RepS, ns, RepG, ng, mat,
        h, k, chi, ind_r, r, row, i, coeff,
        ind_transition, ind_groupe, x, lp, g, ind_l_class;

  Rec := LClassRadical(S, e);
  Rad := Rec.rad;
  LHH := Rec.HList;
  map := Rec.morph;
  l_transitions := Rec.transitions;
  l_returns     := Rec.returns;

  #return l_transitions;
  ListLClass    := List(l_transitions, l -> LClass(S, e * l)); # La composition est dans le sens inverse
  if Length(Rad) = 0 then
    Rad := [[0]];
  fi;
  n    := Length(Rad[1]);
  H    := HClass(S, e);
  ord  := Length(LHH);
  B    := Basis(VectorSpace(Rationals, Rad));
  dim  := Length(B);

  #Print(B, "\t", dim, "\t", ListLClass, "\n");

  RepS := SConjugacyClassReps(S);
  ns   := Length(RepS);
  RepG := DConjugacyClassReps(S, DClass(S, e));
  ng   := Length(RepG);

  mat  := List([1 .. ng], x -> List([1 .. ns], x -> 0));

  for h in RepS do
    for k in RepG do
      chi := 0;

      # Computing the contribution to the trace of each basis vector
      for ind_r in [1 .. dim] do
        r   := B[ind_r];
        row := List([1 .. n], x-> 0);

        # Computing the image of the vector
        for i in [1 .. n] do
          coeff := r[i];
          # Les listes commencent à 1 bleurk
          ind_transition := QuoInt(i - 1, ord) + 1;
          ind_groupe := RemInt(i - 1, ord) + 1;
          x := k * LHH[ind_groupe] * l_transitions[ind_transition] * h;
          ind_transition := Position(ListLClass, LClass(S, x));
          if not ind_transition = fail then
            lp := l_returns[ind_transition];
            g  := (e * x * lp) ^ map;
            ind_groupe  := Position(LHH, g);
            ind_l_class := (ind_transition - 1) * ord + ind_groupe;
            row[ind_l_class] := row[ind_l_class] + coeff;
          fi;
        od;
        chi := chi + Coefficients(B, row)[ind_r];
      od;
      mat[Position(RepG, k)][Position(RepS, h)] := chi;
    od;
  od;

  return mat;
end;

ConcatenatedRadicalBicharacters := function(S)
  local idempotents, e, M;

  idempotents := TransversalIdempotents(S);
  M           := [];
  for e in idempotents do
    M := Concatenation(M, RadicalBicharacter(S, e));
  od;

  return M;
end;

SemigroupCharacterTable := function(S)
  local L, R, D;

  L := ConcatenatedLClassBicharacters(S);
  R := ConcatenatedRadicalBicharacters(S);
  D := DiagonalOfCharacterTables(S);

  return Inverse(TransposedMatMutable(D)) * (L - R);
end;

SemigroupCartanMatrix := function(S)
  local C, M;

  C := SemigroupCharacterTable(S);
  M := TableRegularRepresentationBiCharacter(S);

  return Inverse(TransposedMatMutable(C)) * M * Inverse(C);
end;
