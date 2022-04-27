import Lake

open Lake DSL

package UniverseAbstractions {
  defaultFacet := PackageFacet.oleans,
  dependencies := #[{
    name := `Qq
    src := Source.git "https://github.com/SReichelt/quote4.git" "7bc102c32a5e44b37e918474aabb58c19484d6eb"
  }]
}
