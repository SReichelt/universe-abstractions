import Lake

open Lake DSL

package UniverseAbstractions {
  defaultFacet := PackageFacet.oleans,
  dependencies := #[{
    name := `Qq
    src := Source.git "https://github.com/SReichelt/quote4.git" "1e335e6bb004961435d7ca8911f6fc267e3e5d60"
  }]
}
