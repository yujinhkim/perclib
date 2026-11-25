"use strict";
const toggle = document.querySelector("#menu-toggle");
const sidebar = document.querySelector("#sidebar");
const mobile = matchMedia("(max-width:850px)");
function setMenu(open) {
  document.body.classList.toggle("menu-open", open);
  toggle.setAttribute("aria-expanded", String(open));
  sidebar.inert = mobile.matches && !open;
}
toggle.addEventListener("click", () =>
  setMenu(toggle.getAttribute("aria-expanded") !== "true"),
);
document
  .querySelector("#mobile-overlay")
  .addEventListener("click", () => setMenu(false));
mobile.addEventListener("change", () => setMenu(false));
document.addEventListener("keydown", (e) => {
  if (e.key === "Escape") {
    setMenu(false);
    toggle.focus();
  }
});
setMenu(false);
const form = document.querySelector("#search-form");
if (form) {
  const input = form.elements.q;
  const results = document.querySelector("#search-results");
  const status = document.querySelector("#search-status");
  const normalize = (text) =>
    text
      .normalize("NFKD")
      .replace(/[\u0300-\u036f]/g, "")
      .toLowerCase();
  let index;
  const render = () => {
    if (!index) return;
    const terms = normalize(input.value).trim().split(/\s+/).filter(Boolean);
    const matches = index.filter((row) =>
      terms.every((t) => normalize(row.text).includes(t)),
    );
    results.replaceChildren();
    status.textContent = `${matches.length} results`;
    for (const row of matches) {
      const a = document.createElement("a");
      a.className = "item-row";
      a.href = row.url;
      const span = document.createElement("span");
      span.className = "item-main";
      const title = document.createElement("span");
      title.className = "item-title";
      title.textContent = row.title;
      const summary = document.createElement("span");
      summary.className = "item-desc";
      summary.textContent = row.summary;
      span.append(title, summary);
      a.append(span);
      results.append(a);
    }
  };
  input.value = new URLSearchParams(location.search).get("q") || "";
  fetch("/search-index.json")
    .then((r) => {
      if (!r.ok) throw Error("Search unavailable");
      return r.json();
    })
    .then((data) => {
      index = data;
      render();
    })
    .catch(() => {
      status.textContent =
        "Search could not load. Browse the article index below.";
    });
  input.addEventListener("input", render);
  form.addEventListener("submit", (e) => {
    e.preventDefault();
    history.replaceState(null, "", "?q=" + encodeURIComponent(input.value));
    render();
  });
}
