import os
import re

source_dir = "PMADLean"
files_to_scan = [f for f in os.listdir(source_dir) if f.endswith(".lean")]
#NOTE: DONT USE ANY IN `decl_pattern` IN COMMENTS IN
# Keep your exact pattern and blacklists completely untouched
decl_pattern = re.compile(r'\b(?:theorem|lemma|def|structure|inductive)\s+([A-Za-z0-9_\.]+)')
tactics_blacklist = {'have', 'rw', 'using', 'unfold', 'of', 'block'}

file_declarations = {}
decl_to_full_id = {}
def_nodes = set()          
node_complexity = {}       
cross_dependencies = {}

# FIRST PASS: Extract declarations and pre-categorize trivial proofs based on file contents
for filename in files_to_scan:
    module = filename.replace(".lean", "")
    path = os.path.join(source_dir, filename)
    file_declarations[module] = []
    
    with open(path, "r", encoding="utf-8") as f:
        content = f.read()
        
        # Populate declarations
        for match in decl_pattern.finditer(content):
            name = match.group(1)
            if name not in tactics_blacklist:
                full_id = f"{module}_{name}"
                file_declarations[module].append((name, full_id))
                decl_to_full_id[name] = full_id
                
                # FIX: Look at the exact string match text directly to find definitions
                match_text = match.group(0)
                if any(match_text.startswith(kw) for kw in ['def', 'structure', 'inductive']):
                    def_nodes.add(full_id)

        # FIX: Check if blocks contain simple termination tokens *before* rendering loop runs
        blocks = re.split(r'\b(?:theorem|lemma|def|structure|inductive)\s+', content)
        for block in blocks[1:]:
            lines = block.strip().split("\n")
            if not lines or not lines[0]:
                continue
            # FIX: Target strictly the first string item index in the code lines array slice
            header_match = re.match(r'([A-Za-z0-9_\.]+)', lines[0])
            if not header_match:
                continue
            src_short = header_match.group(1)
            if src_short in tactics_blacklist:
                continue
            src_full = f"{module}_{src_short}"
            
            if src_full not in def_nodes:
                body_lower = block.lower()
                if 'rfl' in body_lower or 'le_refl' in body_lower:
                    node_complexity[src_full] = "trivial"
                else:
                    node_complexity[src_full] = "heavy"

# Establish visual grouping boxes to force readable vertical stacking
module_meta = {
    "Axioms": {"title": "Axioms.lean (Foundations)"},
    "Dynamics": {"title": "Dynamics.lean (Attractor Convergence)"},
    "Probability": {"title": "Probability.lean (Born Rule & Bounds)"},
    "Metrics": {"title": "Metrics.lean (Compliance Geometry)"},
    "Renormalization": {"title": "Renormalization.lean (Scale Decay)"},
    "Vorticity": {"title": "Vorticity.lean (Spacetime Synthesis)"},
    "Incompleteness": {"title": "Incompleteness.lean (Decoupled Limits)"},
    "Test": {"title": "Test.lean (spiral-vm runtime example)"},
    "PhyslibBridge": {"title": "PhyslibBridge.lean (Show equivalence with Physlib)"}
}

# Map edge connections cleanly
for filename in files_to_scan:
    module = filename.replace(".lean", "")
    path = os.path.join(source_dir, filename)
    if module not in module_meta:
        continue
        
    with open(path, "r", encoding="utf-8") as f:
        content = f.read()
        
    blocks = re.split(r'\b(?:theorem|lemma|def|structure|inductive)\s+', content)
    for block in blocks[1:]:
        lines = block.strip().split("\n")
        if not lines or not lines[0]:
            continue
        header_match = re.match(r'([A-Za-z0-9_\.]+)', lines[0])
        if not header_match:
            continue
            
        src_short = header_match.group(1)
        if src_short in tactics_blacklist:
            continue
        src_full = f"{module}_{src_short}"
        
        tokens = re.findall(r'\b([A-Za-z0-9_\.]+)\b', block)
        for token in tokens:
            if token in decl_to_full_id and token != src_short:
                tgt_full = decl_to_full_id[token]
                
                # Check for cross-module edge transformations
                is_cross = token not in [d[0] for d in file_declarations[module]]
                
                if is_cross:
                    tgt_module = tgt_full.split("_")[0]
                    if src_full not in cross_dependencies:
                        cross_dependencies[src_full] = []
                    cross_dependencies[src_full].append(f"{tgt_module}.{token}")

# Generate a high-scannability vertical layout output tree
md_lines = [
    "# 📐 Lean Project Architecture Map",
    "Below is the strict verification architecture layout compiled directly from source code dependencies.",
    "",
]

modules_order = ["Axioms", "Dynamics", "Probability", "Metrics", "Renormalization", "Vorticity", "Incompleteness", "Test", "PhyslibBridge"]
existing_modules = [m for m in modules_order if m in file_declarations and file_declarations[m]]

for idx, module in enumerate(existing_modules):
    meta = module_meta[module]
    decls = file_declarations[module]
    
    # Structural Visual Pipeline Header
    if idx > 0:
        md_lines.append("```text")
        md_lines.append("       │")
        md_lines.append("       ▼ [Cross-Module Dependency Pipeline]")
        md_lines.append("```")
        
    md_lines.append(f"### 📦 {meta['title']}")
    md_lines.append("<details open>")
    md_lines.append(f"<summary><b>View Module Elements ({len(decls)} items)</b></summary>")
    md_lines.append("")
    
    # Text-Based Visual Map Track inside the collapsible pane
    md_lines.append("```text")
    md_lines.append(f"┌─── [{module}.lean] ──────────────────────────────────────────────────┐")
    for short_name, full_id in decls:
        if full_id in def_nodes:
            tag = "[DEF]"
            icon = "⚙️"
        else:
            complexity = node_complexity.get(full_id, "heavy")
            tag = "[TRIV]" if complexity == "trivial" else "[CORE]"
            icon = "⬜" if complexity == "trivial" else "🔥"
            
        deps = cross_dependencies.get(full_id, [])
        dep_track = f" ➔ Outbound to: {', '.join(deps)}" if deps else ""
        
        # Format a clean visual track row
        md_lines.append(f"│  ├─ {icon} {tag:<6} {short_name:<30} {dep_track}")
    md_lines.append(f"└──────────────────────────────────────────────────────────────────────┘")
    md_lines.append("```")
    md_lines.append("</details>")
    md_lines.append("")

with open("theorem_architecture.md", "w", encoding="utf-8") as out:
    out.write("\n".join(md_lines) + "\n")

print("✔ Optimized high-scannability dashboard written to theorem_architecture.md")

