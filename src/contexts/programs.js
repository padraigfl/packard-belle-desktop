import React, { Component } from "react";
import nanoid from "nanoid";
import * as icons from "../icons";
import * as Applications from "../components/Applications";
import startMenuData from "../data/start";
import desktopData from "../data/desktop";
import { ProgramContext } from ".";

const transformLinks = option => ({
  ...option,
  onClick:
    option.href && !option.onClick
      ? e => {
          e.preventDefault();
          if (
            window.confirm(
              `This will open a new tab to ${option.href}, is that okay?`
            )
          ) {
            window.open(option.href);
          }
        }
      : option.onClick
});

const settings = (injectedData = []) => [
  [
    ...injectedData,
    {
      title: "Printers",
      icon: icons.settingsPrinters16,
      component: "ExplorerWindow",
      isDisabled: true
    },
    {
      title: "Folder Options",
      icon: icons.folderOptions16,
      isDisabled: true
    },
    {
      title: "Active Desktop",
      icon: icons.activeDesktop16,
      isDisabled: true
    }
  ],
  {
    title: "Windows Update...",
    icon: icons.windowsUpdate16
  }
];

const startMenu = (injectedData = [], set, shutDown) => [
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
      options: [
        {
          title: "Support Me?",
          icon: icons.htmlFile16,
          onClick: () => window.open("https://www.buymeacoffee.com/padraig")
        }
      ]
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
    icon: icons.shutDown24,
    onClick: shutDown
  }
];

const sameProgram = a => b => a === b.id;
const notSameProgram = a => b => a !== b.id;

export const addIdsToData = data =>
  Array.isArray(data)
    ? data.map(d => {
        if (Array.isArray(d)) {
          return addIdsToData(d);
        }
        return {
          ...transformLinks(d),
          id: d.id || nanoid(),
          options: addIdsToData(d.options)
        };
      })
    : undefined;

const desktopWithIds = (desktopData = []) =>
  addIdsToData(desktopData).map(entry => {
    const { onClick, ...data } = entry;
    return {
      ...data,
      onDoubleClick: onClick
    };
  });

const mapActions = (open, doubleClick) => entry => {
  if (Array.isArray(entry)) {
    return initialize(open, entry);
  }
  const { onClick, ...nestedData } = entry;
  const onClickAction = !entry.options
    ? (...params) => {
        if (Applications[entry.component]) {
          open(entry);
        }
        if (entry.onClick) {
          entry.onClick(...params);
        }
        if (entry.onDoubleClick) {
          entry.onDoubleClick(...params);
        }
      }
    : undefined;
  return {
    ...nestedData,
    onClick: !doubleClick ? onClickAction : undefined,
    onDoubleClick: doubleClick ? onClick : undefined,
    options: initialize(open, entry.options)
  };
};

export const initialize = (open, data, doubleClick) => {
  const mapFunc = mapActions(open, doubleClick);
  return Array.isArray(data) ? data.map(mapFunc) : undefined;
};

const buildDesktop = (desktopData, open) => [
  ...initialize(p => open()(p), desktopWithIds(desktopData)).map(entry => {
    const { onClick, ...data } = entry;
    return {
      ...data,
      onDoubleClick: onClick
    };
  })
];

class ProgramProvider extends Component {
  static defaultProps = {
    startMenuData,
    desktopData
  };
  state = {
    programs: Object.keys(Applications).reduce(
      (acc, p) => ({
        ...acc,
        [p]: { ...Applications[p], programId: nanoid() }
      }),
      {}
    ),
    startMenu: initialize(
      p => this.open(p),
      addIdsToData(
        startMenu(
          this.props.startMenuData,
          [
            { title: "Ctrl+Alt+Del", onClick: () => this.toggleTaskManager() },
            {
              title: "Control Panel",
              onClick: () => this.toggleSettings(),
              icon: icons.controlPanel16
            }
          ],
          () => this.toggleShutDownMenu()
        )
      )
    ),
    desktop: buildDesktop(this.props.desktopData, () => this.open),
    quickLaunch: [
      {
        onClick: () => this.minimizeAll(),
        icon: icons.activeDesktop16,
        title: "Display Desktop"
      }
    ],
    activePrograms: [],
    openOrder: [],
    settingsDisplay: false,
    shutDownMenu: false
  };

  componentDidMount() {
    const desktopSaved = JSON.parse(window.localStorage.getItem("desktop"));
    if (desktopSaved) {
      this.setState(() => ({
        desktop: buildDesktop(desktopSaved, () => this.open)
      }));
    }
  }

  toggleShutDownMenu = () =>
    this.setState(state => ({ shutDownMenu: !state.shutDownMenu }));
  toggleTaskManager = () =>
    this.setState(state => ({ taskManager: !state.taskManager }));
  toggleSettings = val =>
    this.setState(state => ({
      settingsDisplay: val || !state.settingsDisplay
    }));

  shutDown = () => {
    const desktop = document.querySelector(".desktop");
    if (desktop) {
      desktop.innerHTML = "";
      desktop.classList.add("windowsShuttingDown");
      setTimeout(() => {
        desktop.classList.replace(
          "windowsShuttingDown",
          "itIsNowSafeToTurnOffYourComputer"
        );
        window.localStorage.removeItem("loggedIn");
      }, 3000);
    }
  };

  isProgramActive = programId =>
    this.state.activePrograms.some(sameProgram(programId));

  moveToTop = windowId => {
    const programIndex = this.state.activePrograms.findIndex(
      sameProgram(windowId)
    );
    if (programIndex === -1) {
      return;
    }
    this.setState({
      activePrograms: [
        ...this.state.activePrograms.filter(notSameProgram(windowId)),
        {
          ...this.state.activePrograms[programIndex],
          minimized: false
        }
      ],
      activeId: windowId
    });
  };

  open = (program, options = {}) => {
    // @todo use id instead to avoid weird open handling
    // @todo rename launch to handle multi-window programs
    if (!Applications[program.component]) {
      return;
    }
    if (this.isProgramActive(program.id) && !program.multiInstance) {
      this.moveToTop(program.id);
      return;
    }
    const newProgram = {
      ...program,
      id: nanoid(),
      data: options.new ? {} : program.data,
      title: options.new ? program.component : program.title
    };
    this.setState({
      activePrograms: [...this.state.activePrograms, newProgram],
      openOrder: [...this.state.openOrder, newProgram.id],
      activeId: newProgram.id
    });
  };

  close = (program, exit) => {
    if (!this.isProgramActive(program.id)) {
      return;
    }
    const taskBar = this.state.openOrder.filter(p => p !== program.id);
    this.setState({ openOrder: taskBar });

    if (!program.background || exit) {
      this.exit(program.id);
    }
  };

  exit = programId =>
    this.setState({
      activePrograms: this.state.activePrograms.filter(
        notSameProgram(programId)
      ),
      openOrder: this.state.openOrder.filter(x => x !== programId),
      activeId: null
    });

  minimize = programId => {
    if (!this.isProgramActive(programId)) {
      return;
    } else {
      const programIndex = this.state.activePrograms.findIndex(
        sameProgram(programId)
      );
      this.setState({
        activePrograms: [
          {
            ...this.state.activePrograms[programIndex],
            minimized: true
          },
          ...this.state.activePrograms.filter(prog => prog.id !== programId)
        ],
        activeId: null
      });
    }
  };
  minimizeAll = () =>
    this.setState(state => ({
      activePrograms: state.activePrograms.map(p => ({
        ...p,
        minimized: true
      })),
      activeId: null
    }));

  save = (prog, data, title, location = "desktop") => {
    const mapFunc = mapActions(this.open, location === "desktop");
    const existing = this.state[location].find(
      p => p.title === title || p.id === prog.id
    );
    if (existing) {
      return this.setState(
        state => {
          const filtered = state[location].filter(
            p => p.title !== existing.title
          );
          const updated = {
            ...existing,
            data,
            updated: true
          };
          return {
            [location]: [
              ...filtered,
              mapFunc({
                ...updated,
                onClick: () => this.open(updated)
              })
            ]
          };
        },
        () => this.saveLocally(location)
      );
    } else {
      const newProg = {
        ...prog,
        data: {
          ...data,
          readOnly: false
        },
        title,
        newFile: true,
        id: nanoid(),
        readOnly: false
      };
      return this.setState(
        state => ({
          [location]: [
            ...state[location],
            {
              ...mapFunc({
                ...newProg,
                onClick: () => this.open(newProg)
              })
            }
          ]
        }),
        () => this.saveLocally(location)
      );
    }
  };

  saveLocally = loc =>
    window.localStorage.setItem(loc, JSON.stringify(this.state[loc]));

  render() {
    return (
      <ProgramContext.Provider
        value={{
          ...this.state,
          onOpen: this.open,
          onClose: this.close,
          moveToTop: this.moveToTop,
          toggleTaskManager: this.toggleTaskManager,
          toggleSettings: this.toggleSettings,
          toggleShutDownMenu: this.toggleShutDownMenu,
          shutDown: this.shutDown,
          onMinimize: this.minimize,
          save: this.save
        }}
      >
        {this.props.children}
      </ProgramContext.Provider>
    );
  }
}

export default ProgramProvider;
