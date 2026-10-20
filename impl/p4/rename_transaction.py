"""Validation and atomic buffer replacement for cross-workspace rename.

The caller holds the router's mutation lock while planning and committing.  This
module never writes source files: the committed state is the LSP replay buffer.
"""

import copy
import hashlib


class RenameRefused(ValueError):
    pass


def source_digest(text):
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def affected_documents(inventory, group):
    if not isinstance(inventory, dict) or inventory.get("complete") is not True:
        raise RenameRefused("Dependency inventory is incomplete")
    documents = inventory.get("documents")
    if not isinstance(documents, list) or not documents:
        raise RenameRefused("Dependency inventory has no documents")
    owners = {}
    groups = {}
    packages = {}
    for doc in documents:
        if not isinstance(doc, dict) or not isinstance(doc.get("groups"), list):
            raise RenameRefused("Dependency inventory is malformed")
        key = (doc.get("workspace"), doc.get("uri"))
        if not all(isinstance(x, str) and x for x in key) or key in owners:
            raise RenameRefused("Dependency inventory has duplicate documents")
        owners[key] = doc
        for group_rec in doc["groups"]:
            if not isinstance(group_rec, dict) or any(not isinstance(group_rec.get(k), str) for k in ("group", "pid", "capsule")) or not isinstance(group_rec.get("deps"), list) or any(not isinstance(dep, str) for dep in group_rec["deps"]):
                raise RenameRefused("Dependency inventory has malformed groups")
            gid, pid = group_rec["group"], group_rec["pid"]
            if gid in groups or pid in packages:
                raise RenameRefused("Dependency inventory has duplicate groups or packages")
            groups[gid] = (key, group_rec)
            packages[pid] = gid
    if group not in groups:
        raise RenameRefused("Target group is absent from current captures")
    closure = {groups[group][1]["pid"]}
    while True:
        next_closure = closure | {group_rec["pid"] for _, group_rec in groups.values()
                                  if any(dep in closure for dep in group_rec["deps"])}
        if next_closure == closure:
            break
        closure = next_closure
    affected = {groups[packages[pid]][0] for pid in closure}
    if affected != set(owners):
        raise RenameRefused("Source reference coverage is not certified outside the dependency closure")
    return {key: owners[key] for key in affected}


def _offset(text, position):
    if not isinstance(position, dict) or type(position.get("line")) is not int or type(position.get("character")) is not int:
        raise RenameRefused("Invalid UTF-16 edit position")
    line, column = position["line"], position["character"]
    if line < 0 or column < 0:
        raise RenameRefused("Invalid UTF-16 edit position")
    lines = text.splitlines(keepends=True)
    if line == len(lines) and column == 0:
        return len(text)
    if line >= len(lines):
        raise RenameRefused("Edit position lies outside the buffer")
    content = lines[line]
    base = sum(len(part) for part in lines[:line])
    units = 0
    if column == 0:
        return base
    for index, char in enumerate(content):
        units += 2 if ord(char) > 0xFFFF else 1
        if units == column:
            return base + index + 1
        if units > column:
            raise RenameRefused("Edit splits a UTF-16 surrogate pair")
    raise RenameRefused("Edit position lies outside the line")


def plan_buffer(text, edits):
    ranges = []
    for edit in edits:
        if not isinstance(edit, dict) or not isinstance(edit.get("range"), dict) or not isinstance(edit.get("newText"), str):
            raise RenameRefused("Worker returned a malformed text edit")
        region = edit["range"]
        start = _offset(text, region.get("start"))
        end = _offset(text, region.get("end"))
        if start > end:
            raise RenameRefused("Worker returned an inverted text edit")
        ranges.append((start, end, edit["newText"]))
    ranges.sort()
    for previous, current in zip(ranges, ranges[1:]):
        if previous[1] > current[0] or previous[:2] == current[:2]:
            raise RenameRefused("Worker returned overlapping text edits")
    result = text
    for start, end, replacement in reversed(ranges):
        result = result[:start] + replacement + result[end:]
    return result


def anchor_covered(text, position, edits):
    anchor = _offset(text, position)
    for edit in edits:
        region = edit.get("range") if isinstance(edit, dict) else None
        if isinstance(region, dict) and _offset(text, region.get("start")) <= anchor < _offset(text, region.get("end")):
            return True
    return False


def definition_location(result):
    """A single concrete definition location; ambiguity is a refusal."""
    if isinstance(result, list):
        if len(result) != 1:
            raise RenameRefused("Anchor has no unique definition")
        result = result[0]
    if not isinstance(result, dict):
        raise RenameRefused("Anchor has no definition")
    uri = result.get("targetUri", result.get("uri"))
    region = result.get("targetSelectionRange", result.get("range"))
    if not isinstance(uri, str) or not isinstance(region, dict) or not isinstance(region.get("start"), dict) or not isinstance(region.get("end"), dict):
        raise RenameRefused("Worker returned an invalid definition location")
    return uri, region


def definition_names_group(text, region, names, line):
    if type(line) is not int or line < 1 or region["start"].get("line") != line - 1:
        raise RenameRefused("Definition location does not match the captured group")
    start, end = _offset(text, region["start"]), _offset(text, region["end"])
    selected = text[start:end]
    if not selected or not isinstance(names, list) or len(names) != 1:
        raise RenameRefused("Captured declaration member is ambiguous")
    name = names[0]
    if isinstance(name, list):
        name = ".".join(str(part) for part in name)
    if not isinstance(name, str) or selected not in (name, name.rsplit(".", 1)[-1]):
        raise RenameRefused("Definition selection is not the captured declaration")


def extract_edits(result, expected_versions):
    if not isinstance(result, dict):
        raise RenameRefused("Worker returned no rename plan")
    output = {}
    changes = result.get("changes")
    document_changes = result.get("documentChanges")
    if (changes is None) == (document_changes is None):
        raise RenameRefused("Worker returned ambiguous rename plan")
    if changes is not None:
        if not isinstance(changes, dict):
            raise RenameRefused("Worker returned malformed rename changes")
        rows = [(uri, None, edits) for uri, edits in changes.items()]
    else:
        if not isinstance(document_changes, list):
            raise RenameRefused("Worker returned malformed document changes")
        rows = []
        for change in document_changes:
            if not isinstance(change, dict) or not isinstance(change.get("textDocument"), dict):
                raise RenameRefused("Resource operations are unsupported in a buffer transaction")
            rows.append((change["textDocument"].get("uri"), change["textDocument"].get("version"), change.get("edits")))
    for uri, version, edits in rows:
        if uri not in expected_versions or uri in output or not isinstance(edits, list) or not edits:
            raise RenameRefused("Worker edit is outside or duplicates the affected documents")
        if version is not None and version != expected_versions[uri]:
            raise RenameRefused("Worker edit version is stale")
        output[uri] = copy.deepcopy(edits)
    if not output:
        raise RenameRefused("Worker returned an empty rename plan")
    return output
