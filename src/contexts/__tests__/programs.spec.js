import ProgramProvider from "../programs";

describe("ProgramProvider", () => {
  const component = new ProgramProvider();
  component.setState = val => {
    component.state = {
      ...component.state,
      ...val
    };
  };
  component.state.activePrograms = [
    { id: 1, component: 1 },
    { id: 2 },
    { id: 3 }
  ];
  it("isProgramActive", () => {
    expect(component.isProgramActive({ id: 3 })).toEqual(true);
    expect(component.isProgramActive({ id: 4 })).toEqual(false);
  });
  it("moveOnTop", () => {
    component.moveToTop({ id: 2 });
    expect(component.state.activePrograms[2]).toEqual({ id: 2 });
  });
  it("open", () => {
    component.open({ id: 4 });
    expect(component.isProgramActive({ id: 4 })).toEqual(false);

    component.open({ id: 4, component: 4 });
    expect(component.isProgramActive({ id: 4 })).toEqual(true);

    component.open({ id: 1, component: 1 });
    expect(component.state.activePrograms[3]).toEqual({ id: 1, component: 1 });
  });
  it("exit", () => {
    component.exit({ id: 3 });
    expect(component.isProgramActive({ id: 3 })).toEqual(false);
  });
  it("close", () => {
    component.close({ id: 2 });
    expect(component.isProgramActive({ id: 2 })).toEqual(false);
  });
});
