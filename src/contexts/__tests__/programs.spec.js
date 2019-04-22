import ProgramProvider, { addIdsToData, initialize } from "../programs";

const programs = [
  { id: 1, title: "1", component: "Notepad" },
  { id: 2, title: "2", component: "Notepad" },
  { id: 3, title: "3", component: "Notepad" }
];

const defaults = {
  activePrograms: programs,
  desktop: programs,
  openOrder: [1, 2, 3],
  activeId: 3
};

describe("ProgramProvider", () => {
  const component = new ProgramProvider({
    props: { startMenuData: [], desktopData: [] }
  });
  component.setState = val => {
    if (typeof val !== "function") {
      component.state = {
        ...component.state,
        ...val
      };
    } else {
      component.state = {
        ...component.state,
        ...val(component.state)
      };
    }
  };
  component.state = defaults;

  beforeEach(() => {
    component.setState(defaults);
  });
  it("toggleSettings", () => {
    component.toggleSettings();
    expect(component.state.settingsDisplay).toEqual(true);
    component.toggleSettings("test");
    expect(component.state.settingsDisplay).toEqual("test");
  });
  it("toggleTaskManager", () => {
    component.toggleTaskManager();
    expect(component.state.taskManager).toEqual(true);
    component.toggleTaskManager();
    expect(component.state.taskManager).toEqual(false);
  });
  it("toggleShutDownMenu", () => {
    component.toggleShutDownMenu();
    expect(component.state.shutDownMenu).toEqual(true);
    component.toggleShutDownMenu();
    expect(component.state.shutDownMenu).toEqual(false);
  });
  xit("shutDown", () => {});
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

    component.open({ id: 4, component: "Notepad" });
    expect(component.state.activeId).not.toEqual(1);
    expect(component.state.activeId).not.toEqual(2);
    expect(component.state.activeId).not.toEqual(3);
    expect(component.state.openOrder).toEqual([
      1,
      2,
      3,
      component.state.activeId
    ]);

    const nano_id = component.state.activeId;

    component.open({ id: 1, component: "Notepad" });
    expect(component.state.activeId).toEqual(1);
    expect(component.state.activePrograms.map(v => v.id)).toEqual([
      2,
      3,
      nano_id,
      1
    ]);
  });
  it("exit", () => {
    component.exit(3);
    expect(component.isProgramActive(3)).toEqual(false);
    expect(component.state.activeId).toEqual(null);
    expect(component.state.openOrder).toEqual([1, 2]);
    expect(component.state.activePrograms.map(v => v.id)).toEqual([1, 2]);
  });
  it("opens new window for same component", () => {
    component.open({ id: 5, component: "Notepad", multiInstance: true });
    component.open({ id: 5, component: "Notepad", multiInstance: true });
    expect(typeof component.state.activeId).toEqual("string");
    expect(component.state.openOrder.length).toEqual(5);
  });
  it("close", () => {
    component.close({ id: 2 }, true);
    expect(component.isProgramActive(2)).toEqual(false);
  });
  it("minimize", () => {
    component.minimize(2);
    expect(component.state.activePrograms[0].minimized).toEqual(true);
  });
  it("minimizeAll", () => {
    component.minimizeAll();
    component.state.activePrograms.forEach(p => {
      expect(p.minimized).toEqual(true);
    });
  });
  it("save (new file)", () => {
    console.log(component.state.desktop);
    component.save(programs[0], { test: "testing" }, "18");
    console.log(component.state.desktop);
  });
  it("save (existing file)", () => {
    console.log(component.state.desktop);
    component.save(programs[0], { test: "testing" }, "1");
    console.log(component.state.desktop);
  });
});

describe("helper functions", () => {
  it("addIdsToData", () => {
    expect(addIdsToData([{}, {}]).map(d => !!d.id)).toEqual([true, true]);
  });
  it("desktopWithIds (doubleClick)", () => {
    const func = jest.fn();
    const func2 = (a, b) => a + b;
    let desktop = initialize(func, [{ onClick: func2 }], true);
    expect(desktop.map(d => !!d.onDoubleClick)).toEqual([true]);
    desktop = initialize(func, [{ onClick: func2, component: "b" }]);
    expect(desktop.map(d => d.onClick)).not.toEqual([func2]);
  });
});
