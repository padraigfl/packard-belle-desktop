import ProgramProvider from "../programs";

const defaults = {
  activePrograms: [
    { id: 1, Component: 1 },
    { id: 2, Component: 2 },
    { id: 3, Component: 3 }
  ],
  openOrder: [1, 2, 3],
  activeId: 3
};

describe("ProgramProvider", () => {
  const component = new ProgramProvider();
  component.setState = val => {
    component.state = {
      ...component.state,
      ...val
    };
  };
  component.state = defaults;

  beforeEach(() => {
    component.setState(defaults);
  });
  it("isProgramActive", () => {
    expect(component.isProgramActive(3)).toEqual(true);
    expect(component.isProgramActive(4)).toEqual(false);
  });
  it("moveOnTop", () => {
    component.moveToTop(2);
    expect(component.state.activePrograms[2].id).toEqual(2);
    expect(component.state.activeId).toEqual(2);
    expect(component.state.activePrograms.map(v => v.id)).toEqual([1, 3, 2]);
  });
  it("open", () => {
    component.open({ id: 4 });
    expect(component.isProgramActive(4)).toEqual(false);

    component.open({ id: 4, Component: 4 });
    expect(component.isProgramActive(4)).toEqual(true);
    expect(component.state.activeId).toEqual(4);
    expect(component.state.openOrder).toEqual([1, 2, 3, 4]);
    expect(component.state.activePrograms.map(v => v.id)).toEqual([1, 2, 3, 4]);

    component.open({ id: 1, Component: 1 });
    expect(component.state.activeId).toEqual(1);
    expect(component.state.openOrder).toEqual([1, 2, 3, 4]);
    expect(component.state.activePrograms.map(v => v.id)).toEqual([2, 3, 4, 1]);
  });
  it("exit", () => {
    component.exit(3);
    expect(component.isProgramActive(3)).toEqual(false);
    expect(component.state.activeId).toEqual(null);
    expect(component.state.openOrder).toEqual([1, 2]);
    expect(component.state.activePrograms.map(v => v.id)).toEqual([1, 2]);
  });
  it("opens new window for same component", () => {
    component.open({ id: 5, Component: 5, multiWindow: true });
    component.open({ id: 5, Component: 5, multiWindow: true });
    expect(typeof component.state.activeId).toEqual("string");
    expect(component.state.openOrder.length).toEqual(5);
  });
  it("close", () => {
    component.close({ id: 2 }, true);
    expect(component.isProgramActive(2)).toEqual(false);
  });
});
