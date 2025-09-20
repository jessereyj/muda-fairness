Tactics.vo Tactics.glob Tactics.v.beautified Tactics.required_vo: Tactics.v 
Tactics.vos Tactics.vok Tactics.required_vos: Tactics.v 
MudaCore.vo MudaCore.glob MudaCore.v.beautified MudaCore.required_vo: MudaCore.v 
MudaCore.vos MudaCore.vok MudaCore.required_vos: MudaCore.v 
Sorting.vo Sorting.glob Sorting.v.beautified Sorting.required_vo: Sorting.v MudaCore.vo
Sorting.vos Sorting.vok Sorting.required_vos: Sorting.v MudaCore.vos
Matching.vo Matching.glob Matching.v.beautified Matching.required_vo: Matching.v MudaCore.vo Sorting.vo Tactics.vo
Matching.vos Matching.vok Matching.required_vos: Matching.v MudaCore.vos Sorting.vos Tactics.vos
ClearingPrice.vo ClearingPrice.glob ClearingPrice.v.beautified ClearingPrice.required_vo: ClearingPrice.v MudaCore.vo Matching.vo Tactics.vo
ClearingPrice.vos ClearingPrice.vok ClearingPrice.required_vos: ClearingPrice.v MudaCore.vos Matching.vos Tactics.vos
Temporal.vo Temporal.glob Temporal.v.beautified Temporal.required_vo: Temporal.v MudaCore.vo Matching.vo Tactics.vo
Temporal.vos Temporal.vok Temporal.required_vos: Temporal.v MudaCore.vos Matching.vos Tactics.vos
PriorityFairness.vo PriorityFairness.glob PriorityFairness.v.beautified PriorityFairness.required_vo: PriorityFairness.v MudaCore.vo Sorting.vo Matching.vo Tactics.vo
PriorityFairness.vos PriorityFairness.vok PriorityFairness.required_vos: PriorityFairness.v MudaCore.vos Sorting.vos Matching.vos Tactics.vos
QuantityFairness.vo QuantityFairness.glob QuantityFairness.v.beautified QuantityFairness.required_vo: QuantityFairness.v MudaCore.vo Matching.vo Tactics.vo
QuantityFairness.vos QuantityFairness.vok QuantityFairness.required_vos: QuantityFairness.v MudaCore.vos Matching.vos Tactics.vos
Finality.vo Finality.glob Finality.v.beautified Finality.required_vo: Finality.v MudaCore.vo Matching.vo Temporal.vo Tactics.vo
Finality.vos Finality.vok Finality.required_vos: Finality.v MudaCore.vos Matching.vos Temporal.vos Tactics.vos
Maximality.vo Maximality.glob Maximality.v.beautified Maximality.required_vo: Maximality.v MudaCore.vo Matching.vo Tactics.vo
Maximality.vos Maximality.vok Maximality.required_vos: Maximality.v MudaCore.vos Matching.vos Tactics.vos
RejectionFairness.vo RejectionFairness.glob RejectionFairness.v.beautified RejectionFairness.required_vo: RejectionFairness.v MudaCore.vo Matching.vo Tactics.vo
RejectionFairness.vos RejectionFairness.vok RejectionFairness.required_vos: RejectionFairness.v MudaCore.vos Matching.vos Tactics.vos
All.vo All.glob All.v.beautified All.required_vo: All.v Tactics.vo MudaCore.vo Sorting.vo Matching.vo ClearingPrice.vo Temporal.vo PriorityFairness.vo QuantityFairness.vo Finality.vo Maximality.vo RejectionFairness.vo
All.vos All.vok All.required_vos: All.v Tactics.vos MudaCore.vos Sorting.vos Matching.vos ClearingPrice.vos Temporal.vos PriorityFairness.vos QuantityFairness.vos Finality.vos Maximality.vos RejectionFairness.vos
