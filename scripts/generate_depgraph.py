#!/usr/bin/env python3
"""Generate interactive dependency graph HTML from registry JSONL files.

Uses vis.js (bundled from scripts/vendor/vis-network.min.js) to create
a self-contained, hosting-agnostic HTML page with all links relative.

Usage:
    python3 generate_depgraph.py --output depgraph.html --registry-dir ../registry
"""

import json
import argparse
from pathlib import Path


BOOK_COLORS = {
    "I":   "#8fb6ff",      # Categorical Foundations — blue
    "II":  "#b08cff",      # Categorical Holomorphy — purple
    "III": "#86efff",      # Categorical Spectrum — cyan
    "IV":  "#95f3a1",      # Categorical Microcosm — green
    "V":   "#ffb24d",      # Categorical Macrocosm — amber
    "VI":  "#ff6156",      # Categorical Life — red
    "VII": "#c8d4e8",      # Categorical Metaphysics — ink-200 (visible on all bgs)
}

SCOPE_COLORS = {
    "established":  "#8fb6ff",      # Book I blue
    "tau-effective": "#95f3a1",      # Book IV green
    "conjectural":  "#ffb24d",      # Book V amber
    "metaphorical": "#a9b8d0",      # ink-300 (muted)
    "framework":    "#b28fff",      # accent lavender
}

BOOK_NAMES = {
    "I":   "Categorical Foundations",
    "II":  "Categorical Holomorphy",
    "III": "Categorical Spectrum",
    "IV":  "Categorical Microcosm",
    "V":   "Categorical Macrocosm",
    "VI":  "Categorical Life",
    "VII": "Categorical Metaphysics",
}


def load_all_registries(registry_dir):
    """Load all 7 books' JSONL entries."""
    all_entries = []
    for bnum in range(1, 8):
        path = Path(registry_dir) / f"book{bnum}_registry.jsonl"
        if not path.exists():
            continue
        with open(path) as f:
            for line in f:
                line = line.strip()
                if line:
                    try:
                        all_entries.append(json.loads(line))
                    except json.JSONDecodeError:
                        pass
    return all_entries


def build_graph_data(entries):
    """Convert registry entries to vis.js nodes and edges."""
    entry_ids = {e["id"] for e in entries}
    nodes = []
    edges = []

    for entry in entries:
        eid = entry["id"]
        book = entry.get("book", "?")
        scope = entry.get("scope", "unknown")
        formalization = entry.get("formalization", "unknown")
        depended_by = entry.get("depended_by", [])
        lean_module = entry.get("lean_module", "")
        name = entry.get("name", eid)
        summary = entry.get("summary", "")[:120]
        etype = entry.get("type", "unknown")

        # Node size proportional to dependents count (clamped)
        n_deps = len(depended_by)
        size = max(4, min(25, 4 + n_deps * 0.3))

        # Color by scope
        color = SCOPE_COLORS.get(scope, "#cccccc")

        # Border style by formalization
        border_width = 2 if formalization == "formalized" else 1
        dashes = formalization != "formalized"

        # Doc page URL (relative) from lean_module
        doc_url = ""
        if lean_module:
            doc_url = lean_module.replace(".", "/") + ".html"

        node = {
            "id": eid,
            "label": eid,
            "title": f"<b>{eid}</b>: {name}<br><i>{etype}</i> ({scope})<br>{summary}",
            "group": book,
            "size": round(size, 1),
            "color": {
                "background": color,
                "border": "#09101d" if formalization == "formalized" else "#a9b8d0",
                "highlight": {"background": color, "border": "#b28fff"},
            },
            "borderWidth": border_width,
            "font": {"size": 8, "color": "#121a2a"},
            "docUrl": doc_url,
        }
        if dashes:
            node["shapeProperties"] = {"borderDashes": [4, 4]}

        nodes.append(node)

        # Edges: from dependency to this node
        for dep_id in entry.get("depends_on", []):
            if dep_id in entry_ids:
                edges.append({"from": dep_id, "to": eid})

    return nodes, edges


def generate_html(nodes, edges, vis_js_path, output_path):
    """Write self-contained HTML with inline vis.js and graph data."""

    # Load vis.js
    vis_js = ""
    if vis_js_path and Path(vis_js_path).exists():
        vis_js = Path(vis_js_path).read_text(encoding="utf-8")
    else:
        vis_js = "/* vis-network.min.js not found — graph will not render */"
        print(f"WARNING: vis.js not found at {vis_js_path}")

    # Serialize graph data
    nodes_json = json.dumps(nodes)
    edges_json = json.dumps(edges)

    # Book options for filter
    book_options = "\n".join(
        f'      <option value="{roman}">{roman} &mdash; {name}</option>'
        for roman, name in BOOK_NAMES.items()
    )
    scope_checkboxes = "\n".join(
        f'      <label style="margin-right: 12px;">'
        f'<input type="checkbox" class="scope-filter" value="{scope}" checked> '
        f'<span style="display:inline-block;width:10px;height:10px;border-radius:50%;'
        f'background:{color};vertical-align:middle;margin-right:2px;"></span>'
        f'{scope}</label>'
        for scope, color in SCOPE_COLORS.items()
    )

    html = f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>TauLib &mdash; Dependency Graph</title>
<style>
  @font-face {{
    font-family: 'Manrope';
    src: url('fonts/manrope-latin.woff2') format('woff2');
    font-weight: 400 800;
    font-display: swap;
    unicode-range: U+0000-00FF, U+0131, U+0152-0153, U+02BB-02BC, U+02C6,
                   U+02DA, U+02DC, U+0304, U+0308, U+0329, U+2000-206F,
                   U+20AC, U+2122, U+2191, U+2193, U+2212, U+2215, U+FEFF, U+FFFD;
  }}
  @font-face {{
    font-family: 'Manrope';
    src: url('fonts/manrope-latin-ext.woff2') format('woff2');
    font-weight: 400 800;
    font-display: swap;
    unicode-range: U+0100-02AF, U+0304, U+0308, U+0329, U+1E00-1E9F,
                   U+1EF2-1EFF, U+2020, U+20A0-20AB, U+20AD-20C0, U+2113,
                   U+2C60-2C7F, U+A720-A7FF;
  }}

  :root {{
    --pr-bg: #f7f4ee;
    --pr-surface: #ffffff;
    --pr-text: #121a2a;
    --pr-text-muted: #32415b;
    --pr-accent: #b28fff;
    --pr-border: #dce5f2;
    --pr-header-bg: #09101d;
    --pr-header-text: #f6fbff;
    --pr-shadow: 0 4px 16px rgba(18, 26, 42, 0.08);
    --pr-transition: 200ms cubic-bezier(.22, 1, .36, 1);
  }}

  @media (prefers-color-scheme: dark) {{
    :root {{
      --pr-bg: #0b1020;
      --pr-surface: rgba(11, 16, 32, 0.95);
      --pr-text: #f6fbff;
      --pr-text-muted: #a9b8d0;
      --pr-border: #172033;
      --pr-header-bg: #03060f;
      --pr-shadow: 0 4px 16px rgba(0, 0, 0, 0.4);
    }}
  }}

  *, *::before, *::after {{ box-sizing: border-box; }}

  body {{
    font-family: 'Manrope', system-ui, -apple-system, "Segoe UI", sans-serif;
    margin: 0; padding: 0;
    background: var(--pr-bg);
    color: var(--pr-text);
    -webkit-font-smoothing: antialiased;
    -moz-osx-font-smoothing: grayscale;
  }}
  #controls {{
    padding: 12px 20px;
    background: var(--pr-header-bg);
    color: var(--pr-header-text);
    display: flex;
    flex-wrap: wrap;
    align-items: center;
    gap: 12px;
    font-size: 0.9em;
  }}
  #controls a {{ color: var(--pr-accent); text-decoration: none; text-underline-offset: 2px; transition: opacity var(--pr-transition); }}
  #controls a:hover {{ opacity: 0.8; text-decoration: underline; }}
  #controls select, #controls input {{
    font-family: inherit;
    padding: 4px 8px;
    border: 1px solid var(--pr-text-muted);
    border-radius: 8px;
    background: #03060f;
    color: var(--pr-header-text);
    font-size: 0.9em;
    transition: border-color var(--pr-transition);
  }}
  #controls select:focus, #controls input:focus {{
    outline: none;
    border-color: var(--pr-accent);
    box-shadow: 0 0 0 2px rgba(178, 143, 255, 0.3);
  }}
  #controls label {{ color: var(--pr-text-muted); font-size: 0.85em; transition: color var(--pr-transition); }}
  #controls label:hover {{ color: var(--pr-header-text); }}
  #graph-container {{
    width: 100%;
    height: calc(100vh - 100px);
    border-top: 3px solid transparent;
    border-image: linear-gradient(90deg, #7fb3ff, #b28fff, #80ebff, #8ff0b0, #ffbd58, #ff6b62) 1;
  }}
  #info-panel {{
    position: absolute;
    bottom: 20px;
    right: 20px;
    background: var(--pr-surface);
    border: 1px solid var(--pr-border);
    border-radius: 12px;
    padding: 14px 18px;
    max-width: 380px;
    font-size: 0.85em;
    display: none;
    box-shadow: var(--pr-shadow);
    backdrop-filter: blur(12px);
    line-height: 1.5;
  }}
  #info-panel a {{ color: var(--pr-accent); }}
  #info-panel small {{ color: var(--pr-text-muted); }}
  #stats-bar {{
    padding: 4px 20px;
    background: var(--pr-bg);
    font-size: 0.8em;
    color: var(--pr-text-muted);
    border-bottom: 1px solid var(--pr-border);
  }}
</style>
<script>
{vis_js}
</script>
</head>
<body>

<div id="controls">
  <a href="index.html">&larr; Docs</a>
  <strong style="margin-right: 8px;">TauLib Dependency Graph</strong>
  <select id="book-filter">
    <option value="all">All Books</option>
{book_options}
  </select>
  <span style="margin-left: 8px;">Scope:</span>
{scope_checkboxes}
  <input id="search-box" type="text" placeholder="Search ID or name..." style="margin-left: auto; min-width: 180px;">
</div>

<div id="stats-bar">Loading graph...</div>

<div id="graph-container"></div>
<div id="info-panel"></div>

<script>
(function() {{
  var allNodes = {nodes_json};
  var allEdges = {edges_json};

  // Build lookup
  var nodeMap = {{}};
  allNodes.forEach(function(n) {{ nodeMap[n.id] = n; }});

  var nodesDataset = new vis.DataSet(allNodes);
  var edgesDataset = new vis.DataSet(allEdges);

  var container = document.getElementById('graph-container');
  var isDark = window.matchMedia && window.matchMedia('(prefers-color-scheme: dark)').matches;
  var edgeBase = isDark ? '#172033' : '#dce5f2';
  var edgeHi = '#b28fff';

  var options = {{
    nodes: {{
      shape: 'dot',
      font: {{ size: 8, color: isDark ? '#f6fbff' : '#121a2a' }},
    }},
    edges: {{
      arrows: {{ to: {{ enabled: true, scaleFactor: 0.4 }} }},
      color: {{ color: edgeBase, highlight: edgeHi, hover: edgeHi, opacity: 0.6 }},
      width: 0.5,
    }},
    physics: {{
      solver: 'forceAtlas2Based',
      forceAtlas2Based: {{
        gravitationalConstant: -30,
        centralGravity: 0.005,
        springLength: 80,
        springConstant: 0.02,
        damping: 0.4,
      }},
      stabilization: {{ iterations: 200, updateInterval: 25 }},
    }},
    interaction: {{
      hover: true,
      tooltipDelay: 100,
      zoomView: true,
      dragView: true,
    }},
    layout: {{ improvedLayout: false }},
  }};

  var network = new vis.Network(container, {{
    nodes: nodesDataset,
    edges: edgesDataset,
  }}, options);

  // Stats bar
  function updateStats() {{
    var visibleNodes = nodesDataset.get().length;
    var visibleEdges = edgesDataset.get().length;
    document.getElementById('stats-bar').textContent =
      visibleNodes + ' nodes, ' + visibleEdges + ' edges (of ' +
      allNodes.length + ' total nodes)';
  }}

  network.on('stabilizationIterationsDone', function() {{
    updateStats();
  }});

  // Click to navigate to doc page
  network.on('doubleClick', function(params) {{
    if (params.nodes.length > 0) {{
      var nodeId = params.nodes[0];
      var node = nodeMap[nodeId];
      if (node && node.docUrl) {{
        window.location.href = node.docUrl;
      }}
    }}
  }});

  // Click to show info panel
  network.on('click', function(params) {{
    var panel = document.getElementById('info-panel');
    if (params.nodes.length > 0) {{
      var nodeId = params.nodes[0];
      var node = nodeMap[nodeId];
      if (node) {{
        var html = '<strong>' + node.id + '</strong><br>' + node.title;
        if (node.docUrl) {{
          html += '<br><br><a href="' + node.docUrl + '">Open in docs &rarr;</a>';
        }}
        html += '<br><small>Double-click to navigate</small>';
        panel.innerHTML = html;
        panel.style.display = 'block';
      }}
    }} else {{
      panel.style.display = 'none';
    }}
  }});

  // Filter by book
  document.getElementById('book-filter').addEventListener('change', function() {{
    applyFilters();
  }});

  // Filter by scope
  document.querySelectorAll('.scope-filter').forEach(function(cb) {{
    cb.addEventListener('change', function() {{ applyFilters(); }});
  }});

  // Search
  var searchTimeout;
  document.getElementById('search-box').addEventListener('input', function() {{
    clearTimeout(searchTimeout);
    searchTimeout = setTimeout(applyFilters, 200);
  }});

  function applyFilters() {{
    var bookVal = document.getElementById('book-filter').value;
    var activeScopes = [];
    document.querySelectorAll('.scope-filter:checked').forEach(function(cb) {{
      activeScopes.push(cb.value);
    }});
    var searchTerm = document.getElementById('search-box').value.toLowerCase();

    // Filter nodes
    var visibleIds = new Set();
    var filteredNodes = allNodes.filter(function(n) {{
      if (bookVal !== 'all' && n.group !== bookVal) return false;
      // scope: check original entry
      var entry = nodeMap[n.id];
      // Extract scope from title
      var scopeMatch = false;
      activeScopes.forEach(function(s) {{
        if (n.title && n.title.indexOf(s) >= 0) scopeMatch = true;
      }});
      if (!scopeMatch) return false;
      if (searchTerm && n.id.toLowerCase().indexOf(searchTerm) < 0 &&
          n.title.toLowerCase().indexOf(searchTerm) < 0) return false;
      return true;
    }});
    filteredNodes.forEach(function(n) {{ visibleIds.add(n.id); }});

    // Filter edges
    var filteredEdges = allEdges.filter(function(e) {{
      return visibleIds.has(e.from) && visibleIds.has(e.to);
    }});

    nodesDataset.clear();
    nodesDataset.add(filteredNodes);
    edgesDataset.clear();
    edgesDataset.add(filteredEdges);

    updateStats();
  }}

}})();
</script>

</body>
</html>
"""

    Path(output_path).parent.mkdir(parents=True, exist_ok=True)
    with open(output_path, "w") as f:
        f.write(html)
    print(f"Dependency graph written to {output_path} "
          f"({len(nodes)} nodes, {len(edges)} edges)")


def main():
    parser = argparse.ArgumentParser(description="Generate TauLib dependency graph")
    parser.add_argument("--output", default="depgraph.html",
                        help="Output HTML file path")
    parser.add_argument("--registry-dir", required=True,
                        help="Path to registry/ directory with JSONL files")
    args = parser.parse_args()

    # Find vis.js
    script_dir = Path(__file__).parent
    vis_js_path = script_dir / "vendor" / "vis-network.min.js"

    print("Loading registries...")
    entries = load_all_registries(args.registry_dir)
    print(f"  Loaded {len(entries)} entries from 7 books")

    print("Building graph data...")
    nodes, edges = build_graph_data(entries)
    print(f"  {len(nodes)} nodes, {len(edges)} edges")

    print("Generating HTML...")
    generate_html(nodes, edges, str(vis_js_path), args.output)


if __name__ == "__main__":
    main()
