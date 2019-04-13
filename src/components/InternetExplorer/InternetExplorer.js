import React, { Component } from "react";
import cx from "classnames";
import nanoid from "nanoid";
import * as icons from "../../icons";
import "./_styles.scss";
import { WindowExplorer } from "packard-belle";
import Window from "../tools/Window";

const noop = () => {};

export const buildMenu = props => [
  {
    title: "File",
    options: [
      { title: "Open", isDisabled: true },
      { title: "Close", onClick: () => props.onClose(props.id) }
    ]
  },
  {
    title: "Help",
    options: [{ title: `About ${props.title}`, isDisabled: true }]
  }
];

const canAccessIframe = id => {
  const iframe = document && document.querySelector(`.${id}`);
  const canAccess =
    iframe &&
    iframe.contentDocument &&
    iframe.contentDocument.body &&
    iframe.contentDocument.body.scrollHeight;
  if (canAccess) {
    return {
      height: iframe.contentDocument.body.scrollHeight,
      width: iframe.contentDocument.body.scrollWidth
    };
  }
};

class InternetExplorer extends Component {
  id = "b".concat(nanoid()).replace("-", "");
  state = {};

  componentDidMount() {
    const desktop = document.querySelector(".desktop");
    this.setState({
      dimensions: {
        height: desktop.innerHeight > 640 ? desktop.innerHeight : 640,
        width: desktop.innerWidth > 640 ? desktop.innerWidth : 640
      }
    });
    setTimeout(this.getIframeDimension, 3000);
  }
  getIframeDimension = () => {
    const iframeDimensions = canAccessIframe(this.id);
    if (iframeDimensions && iframeDimensions !== this.state.dimensions) {
      this.setState({ dimensions: iframeDimensions });
    }
  };
  render() {
    const { props } = this;
    return (
      <Window
        {...props}
        Component={WindowExplorer}
        className={cx("InternetExplorer", props.className)}
        title={`${
          props.data.title || props.title !== "Internet Explorer"
            ? `${props.data.title || props.title} - `
            : ""
        }Internet Explorer`}
        menuOptions={buildMenu(props)}
        minHeight={300}
        minWidth={300}
        explorerOptions={[
          {
            icon: icons.back,
            title: "Back",
            onClick: noop
          },
          {
            icon: icons.forward,
            title: "Forward",
            onClick: noop
          },
          {
            icon: icons.ieStop,
            title: "Stop",
            onClick: noop
          },
          {
            icon: icons.ieRefresh,
            title: "Refresh",
            onClick: noop
          },
          {
            icon: icons.ieHome,
            title: "Home",
            onClick: noop
          },
          [
            {
              icon: icons.ieSearch,
              title: "Search",
              onClick: noop
            },
            {
              icon: icons.ieFavorites,
              title: "Favorites",
              onClick: noop
            },
            {
              icon: icons.ieHistory,
              title: "History",
              onClick: noop
            }
          ],
          {
            icon: icons.ieMail,
            title: "Mail",
            onClick: noop
          },
          {
            icon: icons.iePrint,
            title: "Print",
            onClick: noop
          }
        ]}
        maximizeOnOpen
      >
        {props.data.__html && <div dangerouslySetInnerHTML={props.data} />}
        {props.children}
        {props.data &&
          !props.data.html &&
          props.data.src &&
          (this.state.dimensions ? (
            <div style={{ ...this.state.dimensions }}>
              <iframe
                className={this.id}
                frameBorder="0"
                src={props.data.src}
                title={props.data.src}
                importance="low"
                height="480"
                width="640"
                {...this.state.dimensions}
              />
            </div>
          ) : (
            <iframe
              className={cx(this.id, "crossOrigin")}
              scrolling="no"
              frameBorder="0"
              src={"http://localhost:3000/" || props.data.src}
              title={props.data.src}
              importance="low"
              height="480"
              width="640"
            />
          ))}
      </Window>
    );
  }
}

export default InternetExplorer;

// initialHeight, initialWidth, title, icon, footer, id,
// onClose, onMaximize, isActive, explorerOptions, chidlren, data, customSelect, Component
