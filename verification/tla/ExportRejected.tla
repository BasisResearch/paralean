-------------------------- MODULE ExportRejected --------------------------
EXTENDS Registry

(* Kernel-valid admission does not imply a successful source export. The
   independent invariant below must detect removing the exporter check from
   Buildable, even though SnapshotSafety itself also refers to Buildable. *)
CaseName == [d \in {"helper"} |-> d]
CaseDeps == [d \in {"helper"} |-> {}]
CaseAncestors == [d \in {"helper"} |-> {}]
CaseExportable == {{}}
NoUnexportableCheckpoint == \A n \in Nodes : head[n] \in Exportable
=============================================================================
