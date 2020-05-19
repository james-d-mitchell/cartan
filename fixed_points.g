# Flemme de l'écrire dans l'interpréteur...

LoadPackage("semigroups");

# TO DO: écrire une version des fonctions sans redondance

#####################################################
###   Représentants des caractères-équivalents    ###
#####################################################

TransversalIdempotents := function(S)
  return List(List(RegularDClasses(S), GroupHClass), MultiplicativeNeutralElement);
end;

SConjugacyClassReps := function(S)
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

DConjugacyClassReps := function(S, D)
  # Note: D must be regular.
  local H, HH, out, C, map;

  H   := GroupHClass(D);
  map := IsomorphismPermGroup(H);
  HH  := Range(map);
  map := InverseGeneralMapping(map);
  C   := List(ConjugacyClasses(HH), Representative);
  C   := List(C, x -> x ^ map);

  return C;
end;

# TO DO: exploiter la redondance en donnant par exemple une liste de
# D-classes et en retournant une liste de listes.

#####################################
###   Caractère de la L-Classe    ###
#####################################

LClassBicharacter := function(S, e, RepS)
  local D, H, map, HH, deg, im_e, l_e_box,
        l_mults, l_to_first, l_from_first, l_transitions, l_returns,
        ns, RepG, ng, M, a, g, b, s, ind, l, lp, x, y;

  D   := DClass(S, e);
  H   := HClass(S, e);
  map := IsomorphismPermGroup(H);
  HH  := Range(map);
  deg := DegreeOfTransformationSemigroup(S);

  im_e    := ImageSetOfTransformation(e, deg);
  l_e_box := Position(LambdaOrb(D), im_e);

  l_mults       := LambdaOrbMults(LambdaOrb(D), LambdaOrbSCCIndex(D));
  l_to_first    := l_mults[l_e_box][2];
  l_from_first  := l_mults[l_e_box][1];
  l_transitions := List(LambdaOrbSCC(D), i -> e * l_to_first * l_mults[i][1]);
  l_returns     := List(LambdaOrbSCC(D), i -> l_mults[i][2] * l_from_first * e);

  ns   := Length(RepS);
  RepG := DConjugacyClassReps(S, DClass(S, e));
  ng   := Length(RepG);
  M    := List([1 .. ng], x -> List([1 .. ns], x -> 0));

  for a in [1 .. ng] do
    g := RepG[a];
    for b in [1 .. ns] do
      s := RepS[b];
      for ind in [1 .. Length(l_transitions)] do
        l  := l_transitions[ind];
        lp := l_returns[ind];
        x := g * e * l * s;
        if x in HClass(S, e * l) then
          y := Inverse((l * s * lp)^map);
          if ConjugacyClass(HH, g^map) = ConjugacyClass(HH, y) then
            M[a][b] := M[a][b] + CentralizerOrder(HH, g^map);
          fi;
        fi;
      od;
    od;
  od;

  return M;
end;

ConcatenatedLClassBicharacters := function(S)
  local idempotents, M, RepS, e;

  M           := [];
  RepS        := SConjugacyClassReps(S);
  idempotents := TransversalIdempotents(S);

  for e in idempotents do
    M := Concatenation(M, LClassBicharacter(S, e, RepS));
  od;

  return M;
end;

# TO DO: écrire une version où on ne calcule H et compagnie qu'une seule fois
# par D-classe

######################################
###   Caractère de la régulière    ###
######################################

# Most complete version yet
TableDClasseGeneric := function(S, D, ConjList)
  local G, d, c, M, deg,
        im_d, l_d_box, l_mults, l_to_first, l_from_first,
        ker_d, r_d_box, r_mults, r_to_first, r_from_first,
        a, b, lvals, h, k, i, l, lp, dl, g, pos, total, r, rp, rd;

  G   := SchutzenbergerGroup(D);
  d   := Representative(D);
  c   := Length(ConjList);
  M   := List([1 .. c], x -> List([1 .. c], x -> 0));
  deg := DegreeOfTransformationSemigroup(S);

  # To come and go from the L-classes
  im_d    := ImageSetOfTransformation(d, deg);
  l_d_box := Position(LambdaOrb(D), im_d);

  l_mults      := LambdaOrbMults(LambdaOrb(D), LambdaOrbSCCIndex(D));
  l_to_first   := l_mults[l_d_box][2];
  l_from_first := l_mults[l_d_box][1];

  # To come and go from the R-classes
  ker_d   := FlatKernelOfTransformation(d, deg);
  r_d_box := Position(RhoOrb(D), ker_d);

  r_mults := RhoOrbMults(RhoOrb(D), RhoOrbSCCIndex(D));
  r_to_first   := r_mults[r_d_box][2];
  r_from_first := r_mults[r_d_box][1];

  for a in [1 .. c] do
    h := ConjList[a];
    for b in [1 .. c] do
      k := ConjList[b];

      # To record k acts on each LClass in the DClass
      lvals := ListWithIdenticalEntries(Length(ConjugacyClasses(G)), 0);

      for i in LambdaOrbSCC(D) do
        l  := l_to_first * l_mults[i][1];
        lp := l_mults[i][2] * l_from_first;
        dl := d * l;

        if dl * k in LClass(S, dl) then # Implies k in image stabiliser
          g   := LambdaPerm(S)(d, dl * k * lp);
          pos := Position(ConjugacyClasses(G), ConjugacyClass(G, g));
          lvals[pos] := lvals[pos] + 1;
        fi;
      od;

      total := 0; # total number of fixed points of D for h, k

      for i in RhoOrbSCC(D) do
        r  := r_mults[i][1] * r_to_first;
        rp := r_from_first * r_mults[i][2];
        rd := r * d;

        if h * rd in RClass(S, rd)  then # Implies k in kernel stabiliser
          g     := LambdaPerm(S)(d, rp * h * rd);
          pos   := Position(ConjugacyClasses(G), ConjugacyClass(G, g));
          total := total + lvals[pos] * Size(Centraliser(G, g));
        fi;
      od;

      M[a][b] := total;
    od;
  od;

  return M;
end;

# Itère TableDClasseGeneric sur les D-classes
TableRegularRepresentationBiCharacter := function(S)
  local C, D, DD, n, mat, i, j;

  C := SConjugacyClassReps(S);
  n := Length(C);
  DD := DClasses(S);
  mat := List([1 .. n], x -> List([1 .. n], x -> 0));

  for D in DD do
    mat := mat + TableDClasseGeneric(S, D, C);
  od;

  # for D in DD do
  #   for i in [1 .. n] do
  #     for j in [1 .. n] do
  #       if IsRegularDClass(D) then
  #         mat[i][j] := mat[i][j] + MyCharacterRegular(S, D, C[i], C[j]);
  #       else
  #         mat[i][j] := mat[i][j] + MyCharacterGeneric(S, D, C[i], C[j]);
  #       fi;
  #     od;
  #   od;
  # od;

  return mat;
end;

# To compare, simple fixed point counting
TestTableD := function(S, D, C)
  local c, M, a, h, b, k, s;

  c   := Length(C);
  M   := List([1 .. c], x -> List([1 .. c], x -> 0));

  for a in [1 .. c] do
    h := C[a];
    for b in [1 .. c] do
      k := C[b];

      M[a][b] := Number(D, x -> h * x * k = x);
    od;
  od;

  return M;
end;

TestTableS := function(S)
  local C, n, mat, D, DD;

  C   := SConjugacyClassReps(S);
  n   := Length(C);
  mat := List([1 .. n], x -> List([1 .. n], x -> 0));
  DD  := DClasses(S);

  for D in DD do
    mat := mat + TestTableD(S, D, C);
  od;

  return mat;
end;

# Utilise les astuces dans le cas régulier
MyCharacterRegular := function(S, D, h, k)
  local H, map, HH, e, mults, lvals, l, lp, x, pos, total, r,
        rp, i, to_first, from_first, im_e, ker_e, e_box;

  H   := GroupHClass(D);
  map := IsomorphismPermGroup(H);
  HH  := Range(map);
  e   := MultiplicativeNeutralElement(H);
  im_e  := ImageSetOfTransformation(e, DegreeOfTransformationSemigroup(S));
  e_box := Position(LambdaOrb(D), im_e);

  if H = fail then
    Error();
  elif not e in H then
    Error();
  fi;

  mults := LambdaOrbMults(LambdaOrb(D), LambdaOrbSCCIndex(D));
  # To come back and from the first H-class in the D-class
  to_first   := mults[e_box][2];
  from_first := mults[e_box][1];
  lvals := ListWithIdenticalEntries(Length(ConjugacyClasses(HH)), 0);

  for i in LambdaOrbSCC(D) do
    #Print(i, "\n");
    l  := to_first * mults[i][1];
    lp := mults[i][2] * from_first;
    x := e * l * k * lp;

    if e * l * k in LClass(S, e * l) then
      pos := Position(ConjugacyClasses(HH), ConjugacyClass(HH, (e * l * k * lp) ^ map));
      lvals[pos] := lvals[pos] + 1;
    fi;
  od;

  total := 0; # total number of fixed points

  mults := RhoOrbMults(RhoOrb(D), RhoOrbSCCIndex(D));
  ker_e  := FlatKernelOfTransformation(e, DegreeOfTransformationSemigroup(S));
  e_box := Position(RhoOrb(D), ker_e);
  to_first   := mults[e_box][2];
  from_first := mults[e_box][1];
  for i in RhoOrbSCC(D) do
    r  := mults[i][1] * to_first;
    rp := from_first * mults[i][2];
    x  := rp * h * r * e;
    if h * r * e in RClass(S, r * e)  then
      pos := Position(ConjugacyClasses(HH), ConjugacyClass(HH, (rp * h * r * e) ^ map));
      total := total + lvals[pos] * Size(Centraliser(HH, x ^ map));
    fi;
  od;
  return total;
end;

# Test version, simple fixed points count
MyCharacterGeneric := function(S, D, h, k)
  local deg, lfilt, rfilt, L, R, H, n, r, l, x;

  deg := DegreeOfTransformationSemigroup(S);

  lfilt := function(l)
    return Representative(l) * k in l;
  end;

  rfilt := function(r)
    return h * Representative(r) in r;
  end;

  L := Filtered(LClasses(D), lfilt);
  R := Filtered(RClasses(D), rfilt);
  H := [];
  for r in R do
    Append(H, Filtered(HClasses(r), lfilt));
  od;
  for l in L do
    Append(H, Filtered(HClasses(l), rfilt));
  od;

  n := 0;
  for x in H do
    n := n + Number(x, s -> h * s * k = s);
  od;

  return n;
end;

# TO DO: écrire une version générique qui utilise les groupes de Schutzenberger
# ---> DONE
# En théorie c'est la meme efficacité que l'autre, au calcul de Schut pret.
# En pratique ? A voir.

#############################################
###   Diagonale des tables des groupes    ###
#############################################

DiagonalOfCharacterTables := function(S)
  local C, n, M, idempotents, b, e, G, I, l, i, j;

  C := SConjugacyClassReps(S);
  n := Length(C);
  M := List([1..n], x -> List([1..n], x -> 0));
  idempotents := TransversalIdempotents(S);

  b := 0;
  for e in idempotents do
    G := Range(IsomorphismPermGroup(HClass(S, e)));
    I := Irr(CharacterTable(G));
    l := Length(I);
    for i in [1..l] do
      for j in [1..l] do
        M[i+b][j+b] := I[i][j];
      od;
    od;
    b := b + l;
  od;

  return M;
end;
