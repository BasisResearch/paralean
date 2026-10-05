# F14 agent view (intentionally not a buildable module graph)

Workspace B's file `ws_b/B.lean` holds `helper_b` and `helper_c`; workspace A's
`ws_a/A.lean` holds `helper`, which uses `helper_b`, while `helper_c` uses A's
`helper`. As files, `B ↔ A` would be an import cycle, which Lake rejects. The
declaration graph `helper_b → helper → helper_c` is acyclic. Each workspace
elaborates against the other's published groups, not against these files.

The expected stock export is `Fixtures/F14/{B1,A,B2}.lean`: three files from two
agent files. P1 must produce an equivalent acyclic layout (any file split is fine
if the declarations, statements and dependency IDs match).
