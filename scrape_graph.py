import os
import re

# Target your local code directories
source_dir = "PMADLean"
files_to_scan = [f for f in os.listdir(source_dir) if f.endswith(".lean")]

all_declarations = set()
decl_to_file = {}
file_contents = {}

# Match declarations: theorem, lemma, def, structure, inductive
decl_pattern = re.compile(r'\b(?:theorem|lemma|def|structure|inductive)\s+([A-Za-z0-9_\.]+)')

# Phase 1: Index every local declaration name
for filename in files_to_scan:
    path = os.path.join(source_dir, filename)
    module_name = filename.replace(".lean", "")
    with open(path, "r", encoding="utf-8") as f:
        content = f.read()
        file_contents[filename] = content
        
        for match in decl_pattern.finditer(content):
            decl_name = match.group(1)
            # Fully qualify names to avoid overlapping collisions
            full_name = f"PMADLean_{module_name}_{decl_name}"
            all_declarations.add(full_name)
            # Track raw short name mapping for text matching
            decl_to_file[decl_name] = full_name

# Phase 2: Map references to extract internal dependencies
mermaid_lines = ["graph TD"]
seen_edges = set()

for filename, content in file_contents.items():
    module_name = filename.replace(".lean", "")
    
    # Isolate blocks using an clean declaration splitter split loop
    blocks = re.split(r'\b(?:theorem|lemma|def|structure|inductive)\s+', content)
    
    for block in blocks[1:]:
        lines = block.strip().split("\n")
        if not lines:
            continue
            
        header_match = re.match(r'([A-Za-z0-9_\.]+)', lines[0])
        if not header_match:
            continue
            
        src_short = header_match.group(1)
        src_full = f"PMADLean_{module_name}_{src_short}"
        
        # Tokenize block content to find calls to other indexed local definitions
        tokens = re.findall(r'\b([A-Za-z0-9_\.]+)\b', block)
        for token in tokens:
            if token in decl_to_file and token != src_short:
                tgt_full = decl_to_file[token]
                edge = f"    {src_full} --> {tgt_full}"
                
                if edge not in seen_edges:
                    mermaid_lines.append(edge)
                    seen_edges.add(edge)

# Save output to Markdown file target destination
with open("theorem_architecture.md", "w", encoding="utf-8") as out:
    out.write("\n".join(mermaid_lines) + "\n")

print(f"✔ Done! Mapped {len(seen_edges)} structural theorem arrows straight into theorem_architecture.md.")
