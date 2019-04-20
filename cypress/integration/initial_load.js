describe("The Home Page", function() {
  it("successfully loads", function() {
    cy.visit("http://localhost:3000"); // change URL to match your dev URL
  });

  it("loads desktop", () => {
    expect(localStorage.getItem("loggedIn")).to.be.null;
    cy.wait(10000);
    cy.get(".StartButton").click();
    console.log(localStorage.getItem("loggedIn"));
  });

  it("shuts down", () => {
    console.log(localStorage.getItem("loggedIn"));
    cy.get(".itIsNowSafeToTurnOffYourComputer").should("not.exist");
    cy.get("button[value='Shut Down...']").click();
    cy.wait(1000);
    cy.get(".ShutDown__window").should("be.visible");
    cy.get(".ShutDown__buttons .btn:first-child").click();
    cy.wait(5000);
    cy.get(".itIsNowSafeToTurnOffYourComputer").should("exist");
  });
});
