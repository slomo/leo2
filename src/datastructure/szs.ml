open Str

type szs_status =

     SUC | UNP | SAP | ESA | SAT | FSA | THM |
     EQV | TAC | WEC | ETH | TAU | WTC | WTH |
     CAX | SCA | TCA | WCA | CUP | CSP | ECS |
     CSA | CTH | CEQ | UNC | WCC | ECT | FUN |
     UNS | WUC | WCT | SCC | UCA | NOC |

     NOS | OPN | UNK | ASS | STP | ERR | OSE |
     INE | SYE | SEE | TYE | FOR | USR | RSO |
     TMO | MMO | GUP | INC | IAP | INP | NTT |
     NTY
;;

exception InvalidSzsStatus of string

let szs_status_strings =  [

(SUC, ( "SUC", "Success" ));
(UNP, ( "UNP", "UnsatisfiabilityPreserving" ));
(SAP, ( "SAP", "SatisfiabilityPreserving" ));
(ESA, ( "ESA", "EquiSatisfiable" ));
(SAT, ( "SAT", "Satisfiable" ));
(FSA, ( "FSA", "FinitelySatisfiable" ));
(THM, ( "THM", "Theorem" ));
(EQV, ( "EQV", "Equivalent" ));
(TAC, ( "TAC", "TautologousConclusion" ));
(WEC, ( "WEC", "WeakerConclusion" ));
(ETH, ( "ETH", "EquivalentTheorem" ));
(TAU, ( "TAU", "Tautology" ));
(WTC, ( "WTC", "WeakerTautologousConclusion" ));
(WTH, ( "WTH", "WeakerTheorem" ));
(CAX, ( "CAX", "ContradictoryAxioms" ));
(SCA, ( "SCA", "SatisfiableConclusionContradictoryAxioms" ));
(TCA, ( "TCA", "TautologousConclusionContradictoryAxioms" ));
(WCA, ( "WCA", "WeakerConclusionContradictoryAxioms" ));
(CUP, ( "CUP", "CounterUnsatisfiabilityPreserving" ));
(CSP, ( "CSP", "CounterSatisfiabilityPreserving" ));
(ECS, ( "ECS", "EquiCounterSatisfiable" ));
(CSA, ( "CSA", "CounterSatisfiable" ));
(CTH, ( "CTH", "CounterTheorem" ));
(CEQ, ( "CEQ", "CounterEquivalent" ));
(UNC, ( "UNC", "UnsatisfiableConclusion" ));
(WCC, ( "WCC", "WeakerCounterConclusion" ));
(ECT, ( "ECT", "EquivalentCounterTheorem" ));
(FUN, ( "FUN", "FinitelyUnsatisfiable" ));
(UNS, ( "UNS", "Unsatisfiable" ));
(WUC, ( "WUC", "WeakerUnsatisfiableConclusion" ));
(WCT, ( "WCT", "WeakerCounterTheorem" ));
(SCC, ( "SCC", "SatisfiableCounterConclusionContradictoryAxioms" ));
(UCA, ( "UCA", "UnsatisfiableConclusionContradictoryAxioms" ));
(NOC, ( "NOC", "NoConsequence" ));

(NOS, ( "NOS", "NoSuccess" ));
(OPN, ( "OPN", "Open" ));
(UNK, ( "UNK", "Unknown" ));
(ASS, ( "ASS", "Assumed" ));
(STP, ( "STP", "Stopped" ));
(ERR, ( "ERR", "Error" ));
(OSE, ( "OSE", "OSError" ));
(INE, ( "INE", "InputError" ));
(SYE, ( "SYE", "SyntaxError" ));
(SEE, ( "SEE", "SemanticError" ));
(TYE, ( "TYE", "TypeError" ));
(FOR, ( "FOR", "Forced" ));
(USR, ( "USR", "User" ));
(RSO, ( "RSO", "ResourceOut" ));
(TMO, ( "TMO", "Timeout" ));
(MMO, ( "MMO", "MemoryOut" ));
(GUP, ( "GUP", "GaveUp" ));
(INC, ( "INC", "Incomplete" ));
(IAP, ( "IAP", "Inappropriate" ));
(INP, ( "INP", "InProgress" ));
(NTT, ( "NTT", "NotTried" ));
(NTY, ( "NTY", "NotTriedYet" ));
];;

let szs_relation =
[
( SUC, [ UNP; SAP; CSP; CUP ] );
( UNP, [ ESA ] );
( SAP, [ THM; CSA ] );
( ESA, [ SAT ] );
( SAT, [ EQV; TAC; WEC; FSA; NOC] );
( FSA, [ ] );
( THM, [ EQV; TAC; WEC; CAX ] );
( EQV, [ ETH; TAU ] );
( TAC, [ TAU; WTC ] );
( WEC, [ WTC; WTH ] );
( ETH, [ ] );
( TAU, [ ] );
( WTC, [ ] );
( WTH, [ ] );
( CAX, [ SCA; SCC ] );
( SCA, [ TCA; WCA ] );
( TCA, [ ] );
( WCA, [ ] );
( CUP, [ ECS ] );
( CSP, [ CTH; SAT ] );
( ECS, [ CSA ] );
( CSA, [ CEQ; UNC; WCC; NOC] );
( CTH, [ CAX; WCC; UNC; CEQ] );
( CEQ, [ UNS; ECT ] );
( UNC, [ WUC; UNS ] );
( WCC, [ WCT; WUC ] );
( ECT, [ ] );
( FUN, [ UNS; ECT ] );
( UNS, [ ] );
( WUC, [ ] );
( WCT, [ ] );
( SCC, [ WCA; UCA] );
( UCA, [ ] );
( NOC, [ ] );

( NOS, [ OPN; UNK; ASS ] );
( OPN, [ ] );
( UNK, [ STP; INP; NTT ] );
( ASS, [ ] );
( STP, [ ERR; FOR; GUP ] );
( ERR, [ OSE; INE ] );
( OSE, [ ] );
( INE, [ SYE; SEE ] );
( SYE, [ ] );
( SEE, [ TYE ] );
( TYE, [ ] );
( FOR, [ USR; RSO ] );
( USR, [ ] );
( RSO, [ TMO; MMO ] );
( TMO, [ ] );
( MMO, [ ] );
( GUP, [ RSO; INC; ERR; IAP] );
( INC, [ ] );
( IAP, [ ] );
( INP, [ ] );
( NTT, [ IAP; NTY ] );
( NTY, [ ] )

];;

let szs_read_status string =
  
  let szs_regexp = Str.regexp "% SZS status \\([A-Za-z]+\\) for" in

  let szs_status_string =
    try
      let _matches  = Str.search_forward szs_regexp string 0 in
      Str.matched_group 1 string
    with
    | Not_found ->
      raise (InvalidSzsStatus ( "No szs status line found" ))
  in

  let filter item = match item with
    |  ( _ , ( _ , my_szs_string ))
        when my_szs_string = szs_status_string -> true
    | _ -> false 
  in
  
  try
    fst (List.find filter szs_status_strings)
  with
  | Not_found ->
    raise (InvalidSzsStatus ("No valid szs status"))
;;

let rec szs_is_a (a : szs_status) (b : szs_status) = 
  if a = b then true
  else
    let subvalues = List.assoc b szs_relation in
    List.exists (szs_is_a a) subvalues
;;


    
 
  

