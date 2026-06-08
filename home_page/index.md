---
layout: default
usemathjax: true
---

# Formalizing Error Correcting Codes in Lean 4

## Explore the project

<ul class="link-grid">
  <li>
    <a href="{{ '/blueprint/' | relative_url }}">
      <strong>Blueprint (web)</strong>
      <span>The mathematical specification, cross-linked to the Lean code.</span>
    </a>
  </li>
  <li>
    <a href="{{ '/blueprint.pdf' | relative_url }}">
      <strong>Blueprint (PDF)</strong>
      <span>A printable version of the full blueprint.</span>
    </a>
  </li>
  <li>
    <a href="{{ '/blueprint/dep_graph_document.html' | relative_url }}">
      <strong>Dependency graph</strong>
      <span>Visualize formalization progress across all results.</span>
    </a>
  </li>
  <li>
    <a href="{{ '/docs/' | relative_url }}">
      <strong>API documentation</strong>
      <span>Generated reference docs for every definition and theorem.</span>
    </a>
  </li>
  <li>
    <a href="https://github.com/{{ site.repository }}">
      <strong>Source on GitHub</strong>
      <span>Browse the Lean sources, issues, and contribution guide.</span>
    </a>
  </li>
  <li>
    <a href="https://leanprover.zulipchat.com/">
      <strong>Lean Zulip</strong>
      <span>Chat with the Lean community and coordinate work.</span>
    </a>
  </li>
</ul>

## Building locally

You need [`elan`](https://github.com/leanprover/elan) (the Lean toolchain
manager) installed. Then:

```sh
git clone https://github.com/{{ site.repository }}.git
cd LeanECC
lake exe cache get
lake build
```

## Authors

This project is developed by {{ site.author }}.
