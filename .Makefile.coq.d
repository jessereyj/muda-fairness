LTL/Syntax.vo LTL/Syntax.glob LTL/Syntax.v.beautified LTL/Syntax.required_vo: LTL/Syntax.v 
LTL/Syntax.vio: LTL/Syntax.v 
LTL/Syntax.vos LTL/Syntax.vok LTL/Syntax.required_vos: LTL/Syntax.v 
LTL/Semantics.vo LTL/Semantics.glob LTL/Semantics.v.beautified LTL/Semantics.required_vo: LTL/Semantics.v LTL/Syntax.vo
LTL/Semantics.vio: LTL/Semantics.v LTL/Syntax.vio
LTL/Semantics.vos LTL/Semantics.vok LTL/Semantics.required_vos: LTL/Semantics.v LTL/Syntax.vos
LTL/Soundness.vo LTL/Soundness.glob LTL/Soundness.v.beautified LTL/Soundness.required_vo: LTL/Soundness.v LTL/Syntax.vo LTL/Semantics.vo
LTL/Soundness.vio: LTL/Soundness.v LTL/Syntax.vio LTL/Semantics.vio
LTL/Soundness.vos LTL/Soundness.vok LTL/Soundness.required_vos: LTL/Soundness.v LTL/Syntax.vos LTL/Semantics.vos
LTL/Completeness.vo LTL/Completeness.glob LTL/Completeness.v.beautified LTL/Completeness.required_vo: LTL/Completeness.v LTL/Syntax.vo LTL/Semantics.vo LTL/Soundness.vo
LTL/Completeness.vio: LTL/Completeness.v LTL/Syntax.vio LTL/Semantics.vio LTL/Soundness.vio
LTL/Completeness.vos LTL/Completeness.vok LTL/Completeness.required_vos: LTL/Completeness.v LTL/Syntax.vos LTL/Semantics.vos LTL/Soundness.vos
LTL/LTL.vo LTL/LTL.glob LTL/LTL.v.beautified LTL/LTL.required_vo: LTL/LTL.v LTL/Syntax.vo LTL/Semantics.vo LTL/Soundness.vo LTL/Completeness.vo
LTL/LTL.vio: LTL/LTL.v LTL/Syntax.vio LTL/Semantics.vio LTL/Soundness.vio LTL/Completeness.vio
LTL/LTL.vos LTL/LTL.vok LTL/LTL.required_vos: LTL/LTL.v LTL/Syntax.vos LTL/Semantics.vos LTL/Soundness.vos LTL/Completeness.vos
MUDA/Types.vo MUDA/Types.glob MUDA/Types.v.beautified MUDA/Types.required_vo: MUDA/Types.v 
MUDA/Types.vio: MUDA/Types.v 
MUDA/Types.vos MUDA/Types.vok MUDA/Types.required_vos: MUDA/Types.v 
MUDA/State.vo MUDA/State.glob MUDA/State.v.beautified MUDA/State.required_vo: MUDA/State.v MUDA/Types.vo
MUDA/State.vio: MUDA/State.v MUDA/Types.vio
MUDA/State.vos MUDA/State.vok MUDA/State.required_vos: MUDA/State.v MUDA/Types.vos
MUDA/Sorting.vo MUDA/Sorting.glob MUDA/Sorting.v.beautified MUDA/Sorting.required_vo: MUDA/Sorting.v MUDA/Types.vo MUDA/State.vo
MUDA/Sorting.vio: MUDA/Sorting.v MUDA/Types.vio MUDA/State.vio
MUDA/Sorting.vos MUDA/Sorting.vok MUDA/Sorting.required_vos: MUDA/Sorting.v MUDA/Types.vos MUDA/State.vos
MUDA/Matching.vo MUDA/Matching.glob MUDA/Matching.v.beautified MUDA/Matching.required_vo: MUDA/Matching.v MUDA/Types.vo MUDA/State.vo
MUDA/Matching.vio: MUDA/Matching.v MUDA/Types.vio MUDA/State.vio
MUDA/Matching.vos MUDA/Matching.vok MUDA/Matching.required_vos: MUDA/Matching.v MUDA/Types.vos MUDA/State.vos
MUDA/ClearingPrice.vo MUDA/ClearingPrice.glob MUDA/ClearingPrice.v.beautified MUDA/ClearingPrice.required_vo: MUDA/ClearingPrice.v MUDA/Types.vo MUDA/State.vo MUDA/Matching.vo
MUDA/ClearingPrice.vio: MUDA/ClearingPrice.v MUDA/Types.vio MUDA/State.vio MUDA/Matching.vio
MUDA/ClearingPrice.vos MUDA/ClearingPrice.vok MUDA/ClearingPrice.required_vos: MUDA/ClearingPrice.v MUDA/Types.vos MUDA/State.vos MUDA/Matching.vos
MUDA/Transitions.vo MUDA/Transitions.glob MUDA/Transitions.v.beautified MUDA/Transitions.required_vo: MUDA/Transitions.v MUDA/Types.vo MUDA/State.vo MUDA/Sorting.vo MUDA/Matching.vo MUDA/ClearingPrice.vo LTL/Semantics.vo
MUDA/Transitions.vio: MUDA/Transitions.v MUDA/Types.vio MUDA/State.vio MUDA/Sorting.vio MUDA/Matching.vio MUDA/ClearingPrice.vio LTL/Semantics.vio
MUDA/Transitions.vos MUDA/Transitions.vok MUDA/Transitions.required_vos: MUDA/Transitions.v MUDA/Types.vos MUDA/State.vos MUDA/Sorting.vos MUDA/Matching.vos MUDA/ClearingPrice.vos LTL/Semantics.vos
MUDA/MUDA.vo MUDA/MUDA.glob MUDA/MUDA.v.beautified MUDA/MUDA.required_vo: MUDA/MUDA.v MUDA/Types.vo MUDA/State.vo MUDA/Sorting.vo MUDA/Matching.vo MUDA/ClearingPrice.vo MUDA/Transitions.vo
MUDA/MUDA.vio: MUDA/MUDA.v MUDA/Types.vio MUDA/State.vio MUDA/Sorting.vio MUDA/Matching.vio MUDA/ClearingPrice.vio MUDA/Transitions.vio
MUDA/MUDA.vos MUDA/MUDA.vok MUDA/MUDA.required_vos: MUDA/MUDA.v MUDA/Types.vos MUDA/State.vos MUDA/Sorting.vos MUDA/Matching.vos MUDA/ClearingPrice.vos MUDA/Transitions.vos
Fairness/QuantityFairness.vo Fairness/QuantityFairness.glob Fairness/QuantityFairness.v.beautified Fairness/QuantityFairness.required_vo: Fairness/QuantityFairness.v MUDA/State.vo MUDA/Matching.vo MUDA/Transitions.vo
Fairness/QuantityFairness.vio: Fairness/QuantityFairness.v MUDA/State.vio MUDA/Matching.vio MUDA/Transitions.vio
Fairness/QuantityFairness.vos Fairness/QuantityFairness.vok Fairness/QuantityFairness.required_vos: Fairness/QuantityFairness.v MUDA/State.vos MUDA/Matching.vos MUDA/Transitions.vos
Fairness/PriorityFairness.vo Fairness/PriorityFairness.glob Fairness/PriorityFairness.v.beautified Fairness/PriorityFairness.required_vo: Fairness/PriorityFairness.v MUDA/Types.vo MUDA/State.vo MUDA/Sorting.vo MUDA/Matching.vo MUDA/Transitions.vo
Fairness/PriorityFairness.vio: Fairness/PriorityFairness.v MUDA/Types.vio MUDA/State.vio MUDA/Sorting.vio MUDA/Matching.vio MUDA/Transitions.vio
Fairness/PriorityFairness.vos Fairness/PriorityFairness.vok Fairness/PriorityFairness.required_vos: Fairness/PriorityFairness.v MUDA/Types.vos MUDA/State.vos MUDA/Sorting.vos MUDA/Matching.vos MUDA/Transitions.vos
Fairness/Finality.vo Fairness/Finality.glob Fairness/Finality.v.beautified Fairness/Finality.required_vo: Fairness/Finality.v MUDA/State.vo MUDA/Matching.vo MUDA/Transitions.vo
Fairness/Finality.vio: Fairness/Finality.v MUDA/State.vio MUDA/Matching.vio MUDA/Transitions.vio
Fairness/Finality.vos Fairness/Finality.vok Fairness/Finality.required_vos: Fairness/Finality.v MUDA/State.vos MUDA/Matching.vos MUDA/Transitions.vos
Fairness/Maximality.vo Fairness/Maximality.glob Fairness/Maximality.v.beautified Fairness/Maximality.required_vo: Fairness/Maximality.v MUDA/State.vo MUDA/Matching.vo MUDA/Transitions.vo
Fairness/Maximality.vio: Fairness/Maximality.v MUDA/State.vio MUDA/Matching.vio MUDA/Transitions.vio
Fairness/Maximality.vos Fairness/Maximality.vok Fairness/Maximality.required_vos: Fairness/Maximality.v MUDA/State.vos MUDA/Matching.vos MUDA/Transitions.vos
Fairness/RejectionFairness.vo Fairness/RejectionFairness.glob Fairness/RejectionFairness.v.beautified Fairness/RejectionFairness.required_vo: Fairness/RejectionFairness.v MUDA/Types.vo MUDA/State.vo MUDA/Matching.vo MUDA/Transitions.vo
Fairness/RejectionFairness.vio: Fairness/RejectionFairness.v MUDA/Types.vio MUDA/State.vio MUDA/Matching.vio MUDA/Transitions.vio
Fairness/RejectionFairness.vos Fairness/RejectionFairness.vok Fairness/RejectionFairness.required_vos: Fairness/RejectionFairness.v MUDA/Types.vos MUDA/State.vos MUDA/Matching.vos MUDA/Transitions.vos
Fairness/All.vo Fairness/All.glob Fairness/All.v.beautified Fairness/All.required_vo: Fairness/All.v Fairness/QuantityFairness.vo Fairness/PriorityFairness.vo Fairness/Finality.vo Fairness/Maximality.vo Fairness/RejectionFairness.vo
Fairness/All.vio: Fairness/All.v Fairness/QuantityFairness.vio Fairness/PriorityFairness.vio Fairness/Finality.vio Fairness/Maximality.vio Fairness/RejectionFairness.vio
Fairness/All.vos Fairness/All.vok Fairness/All.required_vos: Fairness/All.v Fairness/QuantityFairness.vos Fairness/PriorityFairness.vos Fairness/Finality.vos Fairness/Maximality.vos Fairness/RejectionFairness.vos
