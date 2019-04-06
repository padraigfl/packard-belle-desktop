import React, { Component, createContext } from "react";
import nanoid from "nanoid";
import startMenuData, { find } from "../data/start";
import desktopData from "../data/desktop";
import * as icons from "../icons";
import ExplorerWindow from "../components/ExplorerWindow";

export const ProgramContext = createContext();

const settings = (injectedData = []) => [
  [
    ...injectedData,
    {
      title: "Control Panel",
      icon: icons.controlPanel16,
      Component: ExplorerWindow,
      data: {
        content: "Control panel stuff here"
      },
      onClick: () => {}
    },
    // {
    //   title: "Printers",
    //   icon: icons.controlPanel16,
    //   Component: ExplorerWindow,
    //   isDisabled: true
    // },
    {
      title: "Taskbar & Start Menu...",
      icon: icons.settingsTaskbar16,
      Component: ExplorerWindow,
      onClick: () => {}
    }
    // {
    //   title: "Folder Options",
    //   icon: icons.folderOptions16,
    //   isDisabled: true
    // },
    // {
    //   title: "Active Desktop",
    //   icon: icons.activeDesktop16,
    //    // minimize all
    // }
  ],
  {
    title: "Windows Update...",
    icon: icons.windowsUpdate16
  }
];

const startMenu = (injectedData = [], set) => [
  {
    title: "Windows Update",
    icon: icons.windowsUpdate24,
    isDisabled: true
  },
  [
    ...injectedData,
    {
      title: "Settings",
      icon: icons.settings24,
      options: settings(set)
    },
    {
      title: "Help",
      icon: icons.help24,
      options: []
    },
    {
      title: "Run...",
      icon: icons.run24,
      options: []
    }
  ],
  {
    title: "Log Off",
    icon: icons.logOff24,
    isDisabled: true
  },
  {
    title: "Shut Down...",
    icon: icons.shutDown24
  }
];

const sameProgram = a => b => a.id === b.id;
const notSameProgram = a => b => a.id !== b.id;

const addIdsToData = data =>
  Array.isArray(data)
    ? data.map(d => {
        if (Array.isArray(d)) {
          return addIdsToData(d);
        }
        return {
          ...d,
          id: nanoid(),
          options: addIdsToData(d.options)
        };
      })
    : undefined;

const desktopWithIds = addIdsToData(desktopData).map(entry => {
  const { onClick, ...data } = entry;
  return {
    ...data,
    onDoubleClick: onClick
  };
});

const initialize = (open, data, doubleClick) =>
  Array.isArray(data)
    ? data.map(d => {
        if (Array.isArray(d)) {
          return initialize(open, d);
        }
        const { onClick, ...nestedData } = d;
        const onClickAction = !d.options
          ? (...params) => {
              if (d.Component) {
                open(d);
              }
              if (d.onClick) {
                d.onClick(...params);
              }
              if (d.onDoubleClick) {
                d.onDoubleClick(...params);
              }
            }
          : undefined;
        return {
          ...nestedData,
          onClick: !doubleClick ? onClickAction : undefined,
          onDoubleClick: doubleClick ? onClick : undefined,
          options: initialize(open, d.options)
        };
      })
    : undefined;

class ProgramProvider extends Component {
  state = {
    startMenu: initialize(
      p => this.open(p),
      addIdsToData(
        startMenu(startMenuData, [
          { title: "Ctrl+Alt+Del", onClick: () => this.toggleTaskManager() },
          { title: "Settings", onClick: () => this.toggleSettings() }
        ])
      )
    ),
    desktop: initialize(p => this.open(p), desktopWithIds).map(entry => {
      const { onClick, ...data } = entry;
      return {
        ...data,
        onDoubleClick: onClick
      };
    }),
    activePrograms: [],
    openOrder: [],
    settingsDisplay: false
  };

  toggleTaskManager = () =>
    this.setState(state => ({ taskManager: !state.taskManager }));
  toggleSettings = () =>
    this.setState(state => ({ settingsDisplay: !state.settingsDisplay }));

  isProgramActive = program =>
    this.state.activePrograms.some(sameProgram(program));

  exit = program =>
    this.setState({
      activePrograms: this.state.activePrograms.filter(notSameProgram(program)),
      openOrder: this.state.openOrder.filter(x => x !== program.id),
      activeId: null
    });

  moveToTop = program => {
    const programIndex = this.state.activePrograms.findIndex(
      sameProgram(program)
    );
    if (programIndex === -1) {
      return;
    }
    this.setState({
      activePrograms: [
        ...this.state.activePrograms.filter(notSameProgram(program)),
        {
          ...program,
          minimzed: false
        }
      ],
      activeId: program.id
    });
  };

  open = program => {
    if (!program.Component) {
      return;
    }
    if (this.isProgramActive(program) && !program.multiWindow) {
      this.moveToTop(program);
      return;
    }
    const newProgram = {
      ...program,
      id: program.multiWindow ? nanoid() : program.id
    };
    this.setState({
      activePrograms: [...this.state.activePrograms, newProgram],
      openOrder: [...this.state.openOrder, newProgram.id],
      activeId: newProgram.id
    });
  };

  close = (program, exit) => {
    if (!this.isProgramActive(program)) {
      return;
    }

    const taskBar = this.state.openOrder.filter(p => p !== program.id);
    this.setState({ openOrder: taskBar });

    if (!program.background || exit) {
      this.exit(program);
    }
  };

  minimize = program => {
    if (!this.isProgramActive(program)) {
      return;
    } else {
      this.setState({
        activePrograms: [
          {
            ...program,
            minimized: true
          },
          ...this.state.activePrograms.filter(prog => prog.id !== program.id)
        ],
        activeId: null
      });
    }
  };

  render() {
    return (
      <ProgramContext.Provider
        value={{
          ...this.state,
          onClose: this.close,
          moveToTop: this.moveToTop,
          toggleTaskManager: this.toggleTaskManager,
          toggleSettings: this.toggleSettings,
          onMinimize: this.minimize
        }}
      >
        {this.props.children}
      </ProgramContext.Provider>
    );
  }
}

export default ProgramProvider;
